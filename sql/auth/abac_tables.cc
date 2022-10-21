#include "sql/auth/abac_tables.h"

#include <string.h>
#include <memory>

#include "../sql_update.h"  // compare_records()
#include "lex_string.h"
#include "m_ctype.h"
#include "m_string.h"
#include "my_alloc.h"
#include "my_base.h"
#include "my_dbug.h"
#include "my_inttypes.h"
#include "my_sys.h"
#include "mysql/components/services/bits/psi_bits.h"
#include "mysql/components/services/log_builtins.h"
#include "mysql/mysql_lex_string.h"
#include "mysqld_error.h"
#include "sql/auth/auth_internal.h"
#include "sql/auth/sql_auth_cache.h"
#include "sql/auth/sql_user_table.h"
#include "sql/field.h"
#include "sql/handler.h"
#include "sql/key.h"
#include "sql/mdl.h"
#include "sql/mysqld.h"
#include "sql/records.h"
#include "sql/row_iterator.h"
#include "sql/sql_base.h"
#include "sql/sql_const.h"
#include "sql/table.h"
#include "sql_string.h"
#include "thr_lock.h"
#include "sql/auth/auth_acls.h"

using namespace std;
class THD;

#define MYSQL_POLICY_FIELD_RULE_NAME 0
#define MYSQL_POLICY_FIELD_SELECT_PRIV 1
#define MYSQL_POLICY_FIELD_INSERT_PRIV 2
#define MYSQL_POLICY_FIELD_UPDATE_PRIV 3
#define MYSQL_POLICY_FIELD_DELETE_PRIV 4
#define MYSQL_POLICY_FIELD_CREATE_VIEW_PRIV 5
#define MYSQL_POLICY_FIELD_DROP_PRIV 6
#define MYSQL_POLICY_FIELD_DB_LEVEL 7

#define MYSQL_POLICY_DB_RULE_NAME 0
#define MYSQL_POLICY_DB_DB_NAME 1

#define MYSQL_POLICY_USER_AVAL_FIELD_RULE_NAME 0
#define MYSQL_POLICY_USER_AVAL_FIELD_ATTRIB_NAME 1
#define MYSQL_POLICY_USER_AVAL_FIELD_VALUE 2

#define MYSQL_POLICY_OBJECT_AVAL_FIELD_RULE_NAME 0
#define MYSQL_POLICY_OBJECT_AVAL_FIELD_ATTRIB_NAME 1
#define MYSQL_POLICY_OBJECT_AVAL_FIELD_VALUE 2

#define MYSQL_OBJECT_ATTRIBUTES_ATTRIB_NAME 0
#define MYSQL_USER_ATTRIBUTES_ATTRIB_NAME 0

#define MYSQL_USER_ATTRIB_VAL_USER 0
#define MYSQL_USER_ATTRIB_VAL_HOST 1
#define MYSQL_USER_ATTRIB_VAL_ATTRIB_NAME 2
#define MYSQL_USER_ATTRIB_VAL_ATTRIB_VAL 3

#define MYSQL_OBJECT_ATTRIB_VAL_DB 0
#define MYSQL_OBJECT_ATTRIB_VAL_TABLE 1
#define MYSQL_OBJECT_ATTRIB_VAL_ATTRIB_NAME 2
#define MYSQL_OBJECT_ATTRIB_VAL_ATTRIB_VAL 3

bool modify_rule_in_table(THD *thd, TABLE *table, string rule_name,
												int privs, bool db_level_option, bool delete_option) {
  DBUG_TRACE;
  int ret = 0;

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_POLICY)) return true;

  table->use_all_columns();

  table->field[MYSQL_POLICY_FIELD_RULE_NAME]->store(
								rule_name.c_str(), rule_name.size(), system_charset_info);


	char select_field = (privs & SELECT_ACL) ? 'Y' : 'N';
	char insert_field = (privs & INSERT_ACL) ? 'Y' : 'N';
	char update_field = (privs & UPDATE_ACL) ? 'Y' : 'N';
	char delete_field = (privs & DELETE_ACL) ? 'Y' : 'N';
	char create_view_field = (privs & CREATE_VIEW_ACL) ? 'Y' : 'N';
	char drop_field = (privs & DROP_ACL) ? 'Y' : 'N';
	char db_level = (db_level_option) ? 'Y' : 'N';

  table->field[MYSQL_POLICY_FIELD_SELECT_PRIV]->store(
								&select_field, 1, system_charset_info, CHECK_FIELD_IGNORE);
  table->field[MYSQL_POLICY_FIELD_INSERT_PRIV]->store(
								&insert_field, 1, system_charset_info, CHECK_FIELD_IGNORE);
  table->field[MYSQL_POLICY_FIELD_UPDATE_PRIV]->store(
								&update_field, 1, system_charset_info, CHECK_FIELD_IGNORE);
  table->field[MYSQL_POLICY_FIELD_DELETE_PRIV]->store(
								&delete_field, 1, system_charset_info, CHECK_FIELD_IGNORE); 
  table->field[MYSQL_POLICY_FIELD_CREATE_VIEW_PRIV]->store(
								&create_view_field, 1, system_charset_info, CHECK_FIELD_IGNORE); 
  table->field[MYSQL_POLICY_FIELD_DROP_PRIV]->store(
								&drop_field, 1, system_charset_info, CHECK_FIELD_IGNORE); 
  table->field[MYSQL_POLICY_FIELD_DB_LEVEL]->store(
								&db_level, 1, system_charset_info, CHECK_FIELD_IGNORE); 

	if (!delete_option)
		ret = table->file->ha_write_row(table->record[0]);
	else {
		uchar user_key[MAX_KEY_LENGTH];
		key_copy(user_key, table->record[0], table->key_info,
           table->key_info->key_length);
		ret = table->file->ha_index_read_idx_map(table->record[0], 0, user_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
		if (ret != HA_ERR_KEY_NOT_FOUND) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
	}
	return ret != 0;
}

bool modify_policy_db_in_table(THD *thd, TABLE *table, string rule_name, 
									string db_name, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_POLICY_DB)) return true;

  table->use_all_columns();

	table->field[MYSQL_POLICY_DB_RULE_NAME]->store(rule_name.c_str(), rule_name.size(), system_charset_info);
	table->field[MYSQL_POLICY_DB_DB_NAME]->store(db_name.c_str(), db_name.size(), system_charset_info);

	if (!delete_option)
		ret = table->file->ha_write_row(table->record[0]);
	else {
		uchar user_key[MAX_KEY_LENGTH];
		key_copy(user_key, table->record[0], table->key_info,
           table->key_info->key_length);
		ret = table->file->ha_index_read_idx_map(table->record[0], 0, user_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
		if (ret != HA_ERR_KEY_NOT_FOUND) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
	}
	return ret != 0;
}


bool modify_policy_user_aval_in_table(THD *thd, TABLE *table, string rule_name, 
									string attrib, string value, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_POLICY_USER_AVAL)) return true;

  table->use_all_columns();

	table->field[MYSQL_POLICY_USER_AVAL_FIELD_RULE_NAME]->store(
							rule_name.c_str(), rule_name.size(), system_charset_info);
	table->field[MYSQL_POLICY_USER_AVAL_FIELD_ATTRIB_NAME]->store(
							attrib.c_str(), attrib.size(), system_charset_info);
	table->field[MYSQL_POLICY_USER_AVAL_FIELD_VALUE]->store(
							value.c_str(), value.size(), system_charset_info);
	if (!delete_option)
		ret = table->file->ha_write_row(table->record[0]);
	else {
		uchar user_key[MAX_KEY_LENGTH];
		key_copy(user_key, table->record[0], table->key_info,
           table->key_info->key_length);
		ret = table->file->ha_index_read_idx_map(table->record[0], 0, user_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
		if (ret != HA_ERR_KEY_NOT_FOUND) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
	}
	return ret != 0;
}

bool modify_policy_object_aval_in_table(THD *thd, TABLE *table, string rule_name,
									string attrib, string value, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_POLICY_OBJECT_AVAL)) return true;

  table->use_all_columns();

	table->field[MYSQL_POLICY_OBJECT_AVAL_FIELD_RULE_NAME]->store(
							rule_name.c_str(), rule_name.size(), system_charset_info);
	table->field[MYSQL_POLICY_OBJECT_AVAL_FIELD_ATTRIB_NAME]->store(
							attrib.c_str(), attrib.size(), system_charset_info);
	table->field[MYSQL_POLICY_OBJECT_AVAL_FIELD_VALUE]->store(
							value.c_str(), value.size(), system_charset_info);

	if (!delete_option)
		ret = table->file->ha_write_row(table->record[0]);
	else {
		uchar user_key[MAX_KEY_LENGTH];
		key_copy(user_key, table->record[0], table->key_info,
           table->key_info->key_length);
		ret = table->file->ha_index_read_idx_map(table->record[0], 0, user_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
		if (ret != HA_ERR_KEY_NOT_FOUND) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
	}
	return ret != 0;
}

bool modify_user_attribute_in_table(THD *thd, TABLE *table, 
												string user_attrib, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_USER_ATTRIBUTES)) return true;

  table->use_all_columns();

	table->field[MYSQL_USER_ATTRIBUTES_ATTRIB_NAME]->store(
							user_attrib.c_str(), user_attrib.size(), system_charset_info);
	if (!delete_option) {
		ret = table->file->ha_write_row(table->record[0]);
	} else {
		uchar user_attrib_key[MAX_KEY_LENGTH];
		key_copy(user_attrib_key, table->record[0], table->key_info,
           table->key_info->key_length);
		ret = table->file->ha_index_read_idx_map(table->record[0], 0, user_attrib_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
		if (ret != HA_ERR_KEY_NOT_FOUND) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
	}
	return ret != 0;
}

bool modify_object_attribute_in_table(THD *thd, TABLE *table, 
												string object_attrib, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_OBJECT_ATTRIBUTES)) return true;

  table->use_all_columns();

	table->field[MYSQL_OBJECT_ATTRIBUTES_ATTRIB_NAME]->store(
							object_attrib.c_str(), object_attrib.size(), system_charset_info);
	if (!delete_option) {
		ret = table->file->ha_write_row(table->record[0]);
	} else {
		uchar object_attrib_key[MAX_KEY_LENGTH];
		key_copy(object_attrib_key, table->record[0], table->key_info,
           table->key_info->key_length);
		ret = table->file->ha_index_read_idx_map(table->record[0], 0, object_attrib_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
		if (ret != HA_ERR_KEY_NOT_FOUND) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
	}
	return ret != 0;
}

bool modify_user_attrib_val_in_table(THD *thd, TABLE *table, LEX_USER user, 
						LEX_STRING attrib, std::string value, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;
	uchar user_attrib_val_key[MAX_KEY_LENGTH];

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_USER_ATTRIB_VAL)) return true;

  table->use_all_columns();

	table->field[MYSQL_USER_ATTRIB_VAL_ATTRIB_NAME]->store(attrib.str, attrib.length, system_charset_info);
	table->field[MYSQL_USER_ATTRIB_VAL_ATTRIB_VAL]->store(value.c_str(), value.size(), system_charset_info);
	table->field[MYSQL_USER_ATTRIB_VAL_HOST]->store(user.host.str, user.host.length, system_charset_info);
	table->field[MYSQL_USER_ATTRIB_VAL_USER]->store(user.user.str, user.user.length, system_charset_info);

	key_copy(user_attrib_val_key, table->record[0], table->key_info,
           table->key_info->key_length);
  ret = table->file->ha_index_read_idx_map(table->record[0], 0, user_attrib_val_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
	if (delete_option) {
		if (ret == 0) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
		else return false;
	} else if (ret == HA_ERR_KEY_NOT_FOUND) {
		ret = table->file->ha_write_row(table->record[0]);
	}
	return ret != 0;
}

bool modify_object_attrib_val_in_table(THD *thd, TABLE *table, LEX_CSTRING db_name, LEX_CSTRING table_name,
						LEX_STRING attrib, std::string value, bool delete_option) {
	DBUG_TRACE;
  int ret = 0;
	uchar object_attrib_val_key[MAX_KEY_LENGTH];

  Acl_table_intact table_intact(thd);

  if (table_intact.check(table, ACL_TABLES::TABLE_OBJECT_ATTRIB_VAL)) return true;

  table->use_all_columns();

	table->field[MYSQL_OBJECT_ATTRIB_VAL_DB]->store(db_name.str, db_name.length, system_charset_info);
	table->field[MYSQL_OBJECT_ATTRIB_VAL_TABLE]->store(table_name.str, table_name.length, system_charset_info);
	table->field[MYSQL_OBJECT_ATTRIB_VAL_ATTRIB_NAME]->store(attrib.str, attrib.length, system_charset_info);
	table->field[MYSQL_OBJECT_ATTRIB_VAL_ATTRIB_VAL]->store(value.c_str(), value.size(), system_charset_info);

	key_copy(object_attrib_val_key, table->record[0], table->key_info,
           table->key_info->key_length);
  ret = table->file->ha_index_read_idx_map(table->record[0], 0, object_attrib_val_key,
                                           HA_WHOLE_KEY, HA_READ_KEY_EXACT);
	if (delete_option) {
		if (ret == 0) {
			ret = table->file->ha_delete_row(table->record[0]);
		}
		else return false;
	} else if (ret == HA_ERR_KEY_NOT_FOUND) {
		ret = table->file->ha_write_row(table->record[0]);
	}
	return ret != 0;
}