
#ifndef AST_PRINTER_H
#define AST_PRINTER_H

#include "ast.h"

void print_indent(int depth);

void print_string(string str, int depth);

void print_int(int value, int depth);

void print_char(char value, int depth);
void print_prog(T_prog prog_node, int indent);

void print_typename(E_typename typename, int indent);

void print_op(E_op op, int indent);

void print_exprlist(T_exprlist exprlist_node, int indent);

void print_identexpr(T_expr identexpr_node, int indent);

void print_callexpr(T_expr callexpr_node, int indent);

void print_intexpr(T_expr intexpr_node, int indent);

void print_charexpr(T_expr charexpr_node, int indent);

void print_strexpr(T_expr strexpr_node, int indent);

void print_arrayexpr(T_expr arrayexpr_node, int indent);

void print_unaryexpr(T_expr unaryexpr_node, int indent);

void print_binaryexpr(T_expr binaryexpr_node, int indent);

void print_castexpr(T_expr castexpr_node, int indent);

void print_expr(T_expr expr_node, int indent);

void print_assignstmt(T_stmt assignstmt_node, int indent);

void print_ifstmt(T_stmt ifstmt_node, int indent);

void print_ifelsestmt(T_stmt ifelsestmt_node, int indent);

void print_whilestmt(T_stmt whilestmt_node, int indent);

void print_compoundstmt(T_stmt compoundstmt_node, int indent);

void print_stmt(T_stmt stmt_node, int indent);

void print_stmtlist(T_stmtlist stmtlist_node, int indent);

void print_primitivetype(T_type primitivetype_node, int indent);

void print_pointertype(T_type pointertype_node, int indent);

void print_arraytype(T_type arraytype_node, int indent);

void print_functiontype(T_type functiontype_node, int indent);

void print_type(T_type type_node, int indent);

void print_typelist(T_typelist typelist_node, int indent);

void print_decl(T_decl decl_node, int indent);

void print_decllist(T_decllist decllist_node, int indent);

void print_paramlist(T_paramlist paramlist_node, int indent);

void print_func(T_func func_node, int indent);

void print_funclist(T_funclist funclist_node, int indent);

void print_main(T_main main_node, int indent);


#endif
