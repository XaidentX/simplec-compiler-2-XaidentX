#ifndef TYPECHECK_H
#define TYPECHECK_H

#include <stdbool.h>

#include "ast.h"
#include "table.h"

typedef struct S_scope *T_scope;

struct S_scope {
  T_table table;
  T_scope parent;
};

static T_scope create_scope(T_scope parent);

static void destroy_scope(T_scope scope);

static T_type scope_lookup(T_scope scope, string ident);

/* type error */
static void type_error(char *msg);

/* type comparison */
bool compare_types(T_type type1, T_type type2);

/* top-level constructs */
extern void check_prog(T_prog prog);

static void check_decllist(T_decllist decllist);

static void check_decl(T_decl decl);

static void check_funclist(T_funclist funclist);

static void check_func(T_func func);

static void check_main(T_main main);

/* statements */
static void check_stmtlist(T_stmtlist stmtlist);

static void check_stmt(T_stmt stmt);

static void check_assignstmt(T_stmt stmt);

static void check_ifstmt(T_stmt stmt);

static void check_ifelsestmt(T_stmt stmt);

static void check_whilestmt(T_stmt stmt);

static void check_compoundstmt(T_stmt stmt);

/* expressions */
static void check_expr(T_expr expr);

static void check_identexpr(T_expr expr);

static void check_callexpr(T_expr expr);

static void check_intexpr(T_expr expr);

static void check_charexpr(T_expr expr);

static void check_strexpr(T_expr expr);

static void check_arrayexpr(T_expr expr);

static void check_unaryexpr(T_expr expr);

static void check_binaryexpr(T_expr expr);

static void check_castexpr(T_expr expr);

#endif
