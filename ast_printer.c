
#include <stdio.h>

#include "ast_printer.h"

#define NUM_SYMS 2
static char syms[NUM_SYMS] = { '|', '|' };

void print_indent(int depth) {
  int current_char = 0;
  if (depth > 0) {
    for (int i = 0; i < depth; i++) {
//      printf("%c  ", syms[current_char]);
      printf("|  ");
      current_char = (current_char + 1) % NUM_SYMS;
    }
  }
  printf("+-");
}

void print_string(string str, int depth) {
  print_indent(depth);
  printf("%s\n", str);
}

void print_int(int value, int depth) {
  print_indent(depth);
  printf("%d\n", value);
}

void print_char(char value, int depth) {
  print_indent(depth);
  printf("%d\n", value);
}

void print_prog(T_prog prog_node, int indent) {
  
  if (NULL == prog_node) {
    fprintf(stderr, "FATAL: prog_node is NULL in void print_prog(T_prog prog_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("prog\n");
  indent++;
  print_decllist(prog_node->decllist, indent);
  print_funclist(prog_node->funclist, indent);
  print_main(prog_node->main, indent);
}


void print_typename(E_typename typename, int indent) {
  print_indent(indent);
  switch(typename) {
  case E_typename_int: printf("typename_int\n"); break;
  case E_typename_char: printf("typename_char\n"); break;
  default: fprintf(stderr, "FATAL: unexpected typename kind\n"); exit(1); break;
  }
}


void print_op(E_op op, int indent) {
  print_indent(indent);
  switch(op) {
  case E_op_ref: printf("op_ref\n"); break;
  case E_op_deref: printf("op_deref\n"); break;
  case E_op_plus: printf("op_plus\n"); break;
  case E_op_minus: printf("op_minus\n"); break;
  case E_op_not: printf("op_not\n"); break;
  case E_op_times: printf("op_times\n"); break;
  case E_op_divide: printf("op_divide\n"); break;
  case E_op_mod: printf("op_mod\n"); break;
  case E_op_eq: printf("op_eq\n"); break;
  case E_op_ne: printf("op_ne\n"); break;
  case E_op_lt: printf("op_lt\n"); break;
  case E_op_le: printf("op_le\n"); break;
  case E_op_gt: printf("op_gt\n"); break;
  case E_op_ge: printf("op_ge\n"); break;
  case E_op_and: printf("op_and\n"); break;
  case E_op_or: printf("op_or\n"); break;
  default: fprintf(stderr, "FATAL: unexpected op kind\n"); exit(1); break;
  }
}


void print_exprlist(T_exprlist exprlist_node, int indent) {
  
  if (NULL == exprlist_node) {
    print_indent(indent);
    printf("exprlist(empty)\n");
    return;
  }

  print_indent(indent);
  printf("exprlist\n");
  indent++;
  print_expr(exprlist_node->expr, indent);
  print_exprlist(exprlist_node->tail, indent);
}


void print_identexpr(T_expr identexpr_node, int indent) {
  
  if (NULL == identexpr_node) {
    fprintf(stderr, "FATAL: identexpr_node is NULL in void print_identexpr(T_expr identexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("identexpr\n");
  indent++;
  print_string(identexpr_node->identexpr, indent);
}


void print_callexpr(T_expr callexpr_node, int indent) {
  
  if (NULL == callexpr_node) {
    fprintf(stderr, "FATAL: callexpr_node is NULL in void print_callexpr(T_expr callexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("callexpr\n");
  indent++;
  print_string(callexpr_node->callexpr.ident, indent);
  print_exprlist(callexpr_node->callexpr.args, indent);
}


void print_intexpr(T_expr intexpr_node, int indent) {
  
  if (NULL == intexpr_node) {
    fprintf(stderr, "FATAL: intexpr_node is NULL in void print_intexpr(T_expr intexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("intexpr\n");
  indent++;
  print_int(intexpr_node->intexpr, indent);
}


void print_charexpr(T_expr charexpr_node, int indent) {
  
  if (NULL == charexpr_node) {
    fprintf(stderr, "FATAL: charexpr_node is NULL in void print_charexpr(T_expr charexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("charexpr\n");
  indent++;
  print_char(charexpr_node->charexpr, indent);
}


void print_strexpr(T_expr strexpr_node, int indent) {
  
  if (NULL == strexpr_node) {
    fprintf(stderr, "FATAL: strexpr_node is NULL in void print_strexpr(T_expr strexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("strexpr\n");
  indent++;
  print_string(strexpr_node->strexpr, indent);
}


void print_arrayexpr(T_expr arrayexpr_node, int indent) {
  
  if (NULL == arrayexpr_node) {
    fprintf(stderr, "FATAL: arrayexpr_node is NULL in void print_arrayexpr(T_expr arrayexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("arrayexpr\n");
  indent++;
  print_expr(arrayexpr_node->arrayexpr.expr, indent);
  print_expr(arrayexpr_node->arrayexpr.index, indent);
}


void print_unaryexpr(T_expr unaryexpr_node, int indent) {
  
  if (NULL == unaryexpr_node) {
    fprintf(stderr, "FATAL: unaryexpr_node is NULL in void print_unaryexpr(T_expr unaryexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("unaryexpr\n");
  indent++;
  print_op(unaryexpr_node->unaryexpr.op, indent);
  print_expr(unaryexpr_node->unaryexpr.expr, indent);
}


void print_binaryexpr(T_expr binaryexpr_node, int indent) {
  
  if (NULL == binaryexpr_node) {
    fprintf(stderr, "FATAL: binaryexpr_node is NULL in void print_binaryexpr(T_expr binaryexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("binaryexpr\n");
  indent++;
  print_expr(binaryexpr_node->binaryexpr.left, indent);
  print_op(binaryexpr_node->binaryexpr.op, indent);
  print_expr(binaryexpr_node->binaryexpr.right, indent);
}


void print_castexpr(T_expr castexpr_node, int indent) {
  
  if (NULL == castexpr_node) {
    fprintf(stderr, "FATAL: castexpr_node is NULL in void print_castexpr(T_expr castexpr_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("castexpr\n");
  indent++;
  print_type(castexpr_node->castexpr.type, indent);
  print_expr(castexpr_node->castexpr.expr, indent);
}


void print_expr(T_expr expr_node, int indent) {
  if (NULL == expr_node) {
    fprintf(stderr, "FATAL: expr_node is NULL in void print_expr(T_expr expr_node, int indent)\n");
    exit(1);
  }
  switch (expr_node->kind) {
  case E_identexpr: print_identexpr(expr_node, indent); break;
  case E_callexpr: print_callexpr(expr_node, indent); break;
  case E_intexpr: print_intexpr(expr_node, indent); break;
  case E_charexpr: print_charexpr(expr_node, indent); break;
  case E_strexpr: print_strexpr(expr_node, indent); break;
  case E_arrayexpr: print_arrayexpr(expr_node, indent); break;
  case E_unaryexpr: print_unaryexpr(expr_node, indent); break;
  case E_binaryexpr: print_binaryexpr(expr_node, indent); break;
  case E_castexpr: print_castexpr(expr_node, indent); break;
  default: fprintf(stderr, "FATAL: unexpected expr kind\n"); exit(1); break;
  }
  if (NULL != expr_node->type) {
    print_type(expr_node->type, indent + 1);
  }
}


void print_assignstmt(T_stmt assignstmt_node, int indent) {
  
  if (NULL == assignstmt_node) {
    fprintf(stderr, "FATAL: assignstmt_node is NULL in void print_assignstmt(T_stmt assignstmt_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("assignstmt\n");
  indent++;
  print_expr(assignstmt_node->assignstmt.left, indent);
  print_expr(assignstmt_node->assignstmt.right, indent);
}


void print_ifstmt(T_stmt ifstmt_node, int indent) {
  
  if (NULL == ifstmt_node) {
    fprintf(stderr, "FATAL: ifstmt_node is NULL in void print_ifstmt(T_stmt ifstmt_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("ifstmt\n");
  indent++;
  print_expr(ifstmt_node->ifstmt.cond, indent);
  print_stmt(ifstmt_node->ifstmt.body, indent);
}


void print_ifelsestmt(T_stmt ifelsestmt_node, int indent) {
  
  if (NULL == ifelsestmt_node) {
    fprintf(stderr, "FATAL: ifelsestmt_node is NULL in void print_ifelsestmt(T_stmt ifelsestmt_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("ifelsestmt\n");
  indent++;
  print_expr(ifelsestmt_node->ifelsestmt.cond, indent);
  print_stmt(ifelsestmt_node->ifelsestmt.ifbranch, indent);
  print_stmt(ifelsestmt_node->ifelsestmt.elsebranch, indent);
}


void print_whilestmt(T_stmt whilestmt_node, int indent) {
  
  if (NULL == whilestmt_node) {
    fprintf(stderr, "FATAL: whilestmt_node is NULL in void print_whilestmt(T_stmt whilestmt_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("whilestmt\n");
  indent++;
  print_expr(whilestmt_node->whilestmt.cond, indent);
  print_stmt(whilestmt_node->whilestmt.body, indent);
}


void print_compoundstmt(T_stmt compoundstmt_node, int indent) {
  
  if (NULL == compoundstmt_node) {
    fprintf(stderr, "FATAL: compoundstmt_node is NULL in void print_compoundstmt(T_stmt compoundstmt_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("compoundstmt\n");
  indent++;
  print_decllist(compoundstmt_node->compoundstmt.decllist, indent);
  print_stmtlist(compoundstmt_node->compoundstmt.stmtlist, indent);
}


void print_stmt(T_stmt stmt_node, int indent) {
  if (NULL == stmt_node) {
    fprintf(stderr, "FATAL: stmt_node is NULL in void print_stmt(T_stmt stmt_node, int indent)\n");
    exit(1);
  }
  switch (stmt_node->kind) {
  case E_assignstmt: print_assignstmt(stmt_node, indent); break;
  case E_ifstmt: print_ifstmt(stmt_node, indent); break;
  case E_ifelsestmt: print_ifelsestmt(stmt_node, indent); break;
  case E_whilestmt: print_whilestmt(stmt_node, indent); break;
  case E_compoundstmt: print_compoundstmt(stmt_node, indent); break;
  default: fprintf(stderr, "FATAL: unexpected stmt kind\n"); exit(1); break;
  }
}


void print_stmtlist(T_stmtlist stmtlist_node, int indent) {
  
  if (NULL == stmtlist_node) {
    print_indent(indent);
    printf("stmtlist(empty)\n");
    return;
  }

  print_indent(indent);
  printf("stmtlist\n");
  indent++;
  print_stmt(stmtlist_node->stmt, indent);
  print_stmtlist(stmtlist_node->tail, indent);
}


void print_primitivetype(T_type primitivetype_node, int indent) {
  
  if (NULL == primitivetype_node) {
    fprintf(stderr, "FATAL: primitivetype_node is NULL in void print_primitivetype(T_type primitivetype_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("primitivetype\n");
  indent++;
  print_typename(primitivetype_node->primitivetype, indent);
}


void print_pointertype(T_type pointertype_node, int indent) {
  
  if (NULL == pointertype_node) {
    fprintf(stderr, "FATAL: pointertype_node is NULL in void print_pointertype(T_type pointertype_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("pointertype\n");
  indent++;
  print_type(pointertype_node->pointertype, indent);
}


void print_arraytype(T_type arraytype_node, int indent) {
  
  if (NULL == arraytype_node) {
    fprintf(stderr, "FATAL: arraytype_node is NULL in void print_arraytype(T_type arraytype_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("arraytype\n");
  indent++;
  print_int(arraytype_node->arraytype.size, indent);
  print_type(arraytype_node->arraytype.type, indent);
}


void print_functiontype(T_type functiontype_node, int indent) {
  
  if (NULL == functiontype_node) {
    fprintf(stderr, "FATAL: functiontype_node is NULL in void print_functiontype(T_type functiontype_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("functiontype\n");
  indent++;
  print_typelist(functiontype_node->functiontype.paramtypes, indent);
  print_type(functiontype_node->functiontype.returntype, indent);
}


void print_type(T_type type_node, int indent) {
  if (NULL == type_node) {
    fprintf(stderr, "FATAL: type_node is NULL in void print_type(T_type type_node, int indent)\n");
    exit(1);
  }
  switch (type_node->kind) {
  case E_primitivetype: print_primitivetype(type_node, indent); break;
  case E_pointertype: print_pointertype(type_node, indent); break;
  case E_arraytype: print_arraytype(type_node, indent); break;
  case E_functiontype: print_functiontype(type_node, indent); break;
  default: fprintf(stderr, "FATAL: unexpected type kind\n"); exit(1); break;
  }
}


void print_typelist(T_typelist typelist_node, int indent) {
  
  if (NULL == typelist_node) {
    print_indent(indent);
    printf("typelist(empty)\n");
    return;
  }

  print_indent(indent);
  printf("typelist\n");
  indent++;
  print_type(typelist_node->type, indent);
  print_typelist(typelist_node->tail, indent);
}


void print_decl(T_decl decl_node, int indent) {
  
  if (NULL == decl_node) {
    fprintf(stderr, "FATAL: decl_node is NULL in void print_decl(T_decl decl_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("decl\n");
  indent++;
  print_type(decl_node->type, indent);
  print_string(decl_node->ident, indent);
}


void print_decllist(T_decllist decllist_node, int indent) {
  
  if (NULL == decllist_node) {
    print_indent(indent);
    printf("decllist(empty)\n");
    return;
  }

  print_indent(indent);
  printf("decllist\n");
  indent++;
  print_decl(decllist_node->decl, indent);
  print_decllist(decllist_node->tail, indent);
}


void print_paramlist(T_paramlist paramlist_node, int indent) {
  
  if (NULL == paramlist_node) {
    print_indent(indent);
    printf("paramlist(empty)\n");
    return;
  }

  print_indent(indent);
  printf("paramlist\n");
  indent++;
  print_string(paramlist_node->ident, indent);
  print_paramlist(paramlist_node->tail, indent);
}


void print_func(T_func func_node, int indent) {
  
  if (NULL == func_node) {
    fprintf(stderr, "FATAL: func_node is NULL in void print_func(T_func func_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("func\n");
  indent++;
  print_string(func_node->ident, indent);
  print_paramlist(func_node->paramlist, indent);
  print_type(func_node->type, indent);
  print_decllist(func_node->decllist, indent);
  print_stmtlist(func_node->stmtlist, indent);
  print_expr(func_node->returnexpr, indent);
}


void print_funclist(T_funclist funclist_node, int indent) {
  
  if (NULL == funclist_node) {
    print_indent(indent);
    printf("funclist(empty)\n");
    return;
  }

  print_indent(indent);
  printf("funclist\n");
  indent++;
  print_func(funclist_node->func, indent);
  print_funclist(funclist_node->tail, indent);
}


void print_main(T_main main_node, int indent) {
  
  if (NULL == main_node) {
    fprintf(stderr, "FATAL: main_node is NULL in void print_main(T_main main_node, int indent)\n");
    exit(1);
  }

  print_indent(indent);
  printf("main\n");
  indent++;
  print_decllist(main_node->decllist, indent);
  print_stmtlist(main_node->stmtlist, indent);
  print_expr(main_node->returnexpr, indent);
}

