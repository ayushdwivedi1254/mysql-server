// #include "enclave_t.h"
// #include "sgx_tseal.h"
#include "string.h"

// #include "enclave.h"
// #include "wrapper.h"
#include <unordered_map>
#include <string>

#include "sql/auth/sql_authorization.h"

#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <algorithm>
#include <boost/concept/usage.hpp>
#include <boost/function.hpp>
#include <boost/graph/adjacency_iterator.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/breadth_first_search.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graphml.hpp>
#include <boost/graph/named_function_params.hpp>
#include <boost/graph/properties.hpp>
#include <boost/iterator/iterator_facade.hpp>
#include <boost/move/utility_core.hpp>
#include <boost/property_map/dynamic_property_map.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/range/irange.hpp>
#include <boost/smart_ptr/make_shared_object.hpp>
#include <boost/smart_ptr/shared_ptr.hpp>
#include <boost/tuple/tuple.hpp>
#include <cstdlib>
#include <iterator>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <time.h>

#include "lex_string.h"
#include "m_ctype.h"
#include "m_string.h"
#include "map_helpers.h"
#include "mf_wcomp.h"
#include "my_alloc.h"
#include "my_compiler.h"
#include "my_dbug.h"
#include "my_inttypes.h"
#include "my_loglevel.h"
#include "my_macros.h"
#include "my_sqlcommand.h"
#include "my_sys.h"
#include "mysql/components/services/log_builtins.h"
#include "mysql/components/services/log_shared.h"
#include "mysql/mysql_lex_string.h"
#include "mysql/plugin_audit.h"
#include "mysql/psi/mysql_mutex.h"
#include "mysql/service_mysql_alloc.h"
#include "mysql_com.h"
#include "mysqld_error.h"
#include "prealloced_array.h"
#include "sql/auth/auth_acls.h"
#include "sql/auth/auth_common.h"
#include "sql/auth/auth_internal.h"
#include "sql/auth/auth_utility.h"
#include "sql/auth/dynamic_privilege_table.h"
#include "sql/auth/partial_revokes.h"
#include "sql/auth/role_tables.h"
#include "sql/auth/roles.h"
#include "sql/auth/sql_auth_cache.h"
#include "sql/auth/sql_security_ctx.h"
#include "sql/auth/sql_user_table.h"
#include "sql/auth/abac_tables.h"
#include "sql/current_thd.h"
#include "sql/dd/dd_table.h"  // dd::table_exists
#include "sql/dd/dd_schema.h"  // dd::schema_exists
#include "sql/debug_sync.h"
#include "sql/derror.h"        /* ER_THD */
#include "sql/error_handler.h" /* error_handler */
#include "sql/field.h"
#include "sql/handler.h"
#include "sql/item.h"
#include "sql/key_spec.h" /* Key_spec */
#include "sql/mdl.h"
#include "sql/mysqld.h" /* lower_case_table_names */
#include "sql/nested_join.h"
#include "sql/protocol.h"
#include "sql/sp.h"         /* sp_exist_routines */
#include "sql/sql_admin.h"  // enum role_enum
#include "sql/sql_alter.h"
#include "sql/sql_audit.h"
#include "sql/sql_base.h"  /* open_and_lock_tables */
#include "sql/sql_class.h" /* THD */
#include "sql/sql_connect.h"
#include "sql/sql_error.h"
#include "sql/sql_lex.h"
#include "sql/sql_list.h"
#include "sql/sql_parse.h"   /* get_current_user */
#include "sql/sql_rewrite.h" /* Grant_params */
#include "sql/sql_show.h"    /* append_identifier */
#include "sql/sql_view.h"    /* VIEW_ANY_ACL */
#include "sql/strfunc.h"
#include "sql/system_variables.h"
#include "sql/table.h"
#include "sql/thd_raii.h"
#include "sql_string.h"
#include "template_utils.h"
#include "thr_lock.h"
#include "violite.h"

bool check_table_access(THD *thd, ulong requirements, TABLE_LIST *tables,
                        bool any_combination_of_privileges_will_do, uint number,
                        bool no_errors) {
  DBUG_TRACE;
  TABLE_LIST *org_tables = tables;
  TABLE_LIST *first_not_own_table = thd->lex->first_not_own_table();
  uint i = 0;
  Security_context *sctx = thd->security_context();
  Security_context *backup_ctx = thd->security_context();

  /*
    The check that first_not_own_table is not reached is for the case when
    the given table list refers to the list for prelocking (contains tables
    of other queries). For simple queries first_not_own_table is 0.
  */
  for (; i < number && tables != first_not_own_table && tables;
       tables = tables->next_global, i++) {
    TABLE_LIST *const table_ref =
        tables->correspondent_table ? tables->correspondent_table : tables;
    ulong want_access = requirements;
    if (table_ref->security_ctx)
      sctx = table_ref->security_ctx;
    else
      sctx = backup_ctx;

    /*
      We should not encounter table list elements for reformed SHOW
      statements unless this is first table list element in the main
      query block.
      Such table list elements require additional privilege check
      (see Sql_cmd_show_xxx::check_privileges()).
      This check is carried out by caller, but only for the first table list
      element from the main query block.
    */
    assert(!table_ref->schema_table_reformed ||
           table_ref == thd->lex->query_block->table_list.first);

    DBUG_PRINT("info",
               ("table: %s derived: %d  view: %d", table_ref->table_name,
                table_ref->is_derived(), table_ref->is_view()));

    if (table_ref->is_internal()) continue;

    thd->set_security_context(sctx);

    if (check_access(thd, want_access, table_ref->get_db_name(),
                     &table_ref->grant.privilege, &table_ref->grant.m_internal,
                     false, no_errors)) {
        goto deny;
    }
  }
  thd->set_security_context(backup_ctx);

  DBUG_EXECUTE_IF("force_check_table_access_return_ok", return false;);
  return check_grant(thd, requirements, org_tables,
                     any_combination_of_privileges_will_do, number, no_errors);
deny:
  thd->set_security_context(backup_ctx);
  return true;
}

int ecall_evaluate_aux(int* result, ABAC_TREE_NODE* root, ATTRIB_DICT_WRAPPER* ua, ATTRIB_DICT_WRAPPER* oa, int weekday, int access) {
	*result = evaluate_aux(root->root, ua->attrib_map, oa->attrib_map, weekday, access);
	return RET_SUCCESS;
}
