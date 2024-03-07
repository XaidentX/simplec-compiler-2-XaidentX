
#include "ast.h"

T_prog create_prog(T_decllist decllist, T_funclist funclist, T_main main) {
  if (NULL == main) {
    fprintf(stderr, "FATAL: setting main in create_prog to NULL!\n");
    exit(1);
  }
  T_prog val = xmalloc(sizeof(*val));
  val->decllist = decllist;
  val->funclist = funclist;
  val->main = main;
  return val;
}

T_exprlist create_exprlist(T_expr expr, T_exprlist tail) {
  if (NULL == expr) {
    fprintf(stderr, "FATAL: setting expr in create_exprlist to NULL!\n");
    exit(1);
  }
  T_exprlist val = xmalloc(sizeof(*val));
  val->expr = expr;
  val->tail = tail;
  return val;
}

T_expr create_identexpr(string identexpr) {
  
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_identexpr;
  val->identexpr = identexpr;
  return val;
}

T_expr create_callexpr(string ident, T_exprlist args) {
  
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_callexpr;
  val->callexpr.ident = ident;
  val->callexpr.args = args;
  return val;
}

T_expr create_intexpr(int intexpr) {
  
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_intexpr;
  val->intexpr = intexpr;
  return val;
}

T_expr create_charexpr(char charexpr) {
  
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_charexpr;
  val->charexpr = charexpr;
  return val;
}

T_expr create_strexpr(string strexpr) {
  
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_strexpr;
  val->strexpr = strexpr;
  return val;
}

T_expr create_arrayexpr(T_expr expr, T_expr index) {
  if (NULL == expr) {
    fprintf(stderr, "FATAL: setting expr in create_arrayexpr to NULL!\n");
    exit(1);
  }
  if (NULL == index) {
    fprintf(stderr, "FATAL: setting index in create_arrayexpr to NULL!\n");
    exit(1);
  }
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_arrayexpr;
  val->arrayexpr.expr = expr;
  val->arrayexpr.index = index;
  return val;
}

T_expr create_unaryexpr(E_op op, T_expr expr) {
  if (NULL == expr) {
    fprintf(stderr, "FATAL: setting expr in create_unaryexpr to NULL!\n");
    exit(1);
  }
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_unaryexpr;
  val->unaryexpr.op = op;
  val->unaryexpr.expr = expr;
  return val;
}

T_expr create_binaryexpr(T_expr left, E_op op, T_expr right) {
  if (NULL == left) {
    fprintf(stderr, "FATAL: setting left in create_binaryexpr to NULL!\n");
    exit(1);
  }
  if (NULL == right) {
    fprintf(stderr, "FATAL: setting right in create_binaryexpr to NULL!\n");
    exit(1);
  }
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_binaryexpr;
  val->binaryexpr.left = left;
  val->binaryexpr.op = op;
  val->binaryexpr.right = right;
  return val;
}

T_expr create_castexpr(T_type type, T_expr expr) {
  if (NULL == type) {
    fprintf(stderr, "FATAL: setting type in create_castexpr to NULL!\n");
    exit(1);
  }
  if (NULL == expr) {
    fprintf(stderr, "FATAL: setting expr in create_castexpr to NULL!\n");
    exit(1);
  }
  T_expr val = xmalloc(sizeof(*val));
  val->kind = E_castexpr;
  val->castexpr.type = type;
  val->castexpr.expr = expr;
  return val;
}

T_stmt create_assignstmt(T_expr left, T_expr right) {
  if (NULL == left) {
    fprintf(stderr, "FATAL: setting left in create_assignstmt to NULL!\n");
    exit(1);
  }
  if (NULL == right) {
    fprintf(stderr, "FATAL: setting right in create_assignstmt to NULL!\n");
    exit(1);
  }
  T_stmt val = xmalloc(sizeof(*val));
  val->kind = E_assignstmt;
  val->assignstmt.left = left;
  val->assignstmt.right = right;
  return val;
}

T_stmt create_ifstmt(T_expr cond, T_stmt body) {
  if (NULL == cond) {
    fprintf(stderr, "FATAL: setting cond in create_ifstmt to NULL!\n");
    exit(1);
  }
  if (NULL == body) {
    fprintf(stderr, "FATAL: setting body in create_ifstmt to NULL!\n");
    exit(1);
  }
  T_stmt val = xmalloc(sizeof(*val));
  val->kind = E_ifstmt;
  val->ifstmt.cond = cond;
  val->ifstmt.body = body;
  return val;
}

T_stmt create_ifelsestmt(T_expr cond, T_stmt ifbranch, T_stmt elsebranch) {
  if (NULL == cond) {
    fprintf(stderr, "FATAL: setting cond in create_ifelsestmt to NULL!\n");
    exit(1);
  }
  if (NULL == ifbranch) {
    fprintf(stderr, "FATAL: setting ifbranch in create_ifelsestmt to NULL!\n");
    exit(1);
  }
  if (NULL == elsebranch) {
    fprintf(stderr, "FATAL: setting elsebranch in create_ifelsestmt to NULL!\n");
    exit(1);
  }
  T_stmt val = xmalloc(sizeof(*val));
  val->kind = E_ifelsestmt;
  val->ifelsestmt.cond = cond;
  val->ifelsestmt.ifbranch = ifbranch;
  val->ifelsestmt.elsebranch = elsebranch;
  return val;
}

T_stmt create_whilestmt(T_expr cond, T_stmt body) {
  if (NULL == cond) {
    fprintf(stderr, "FATAL: setting cond in create_whilestmt to NULL!\n");
    exit(1);
  }
  if (NULL == body) {
    fprintf(stderr, "FATAL: setting body in create_whilestmt to NULL!\n");
    exit(1);
  }
  T_stmt val = xmalloc(sizeof(*val));
  val->kind = E_whilestmt;
  val->whilestmt.cond = cond;
  val->whilestmt.body = body;
  return val;
}

T_stmt create_compoundstmt(T_decllist decllist, T_stmtlist stmtlist) {
  
  T_stmt val = xmalloc(sizeof(*val));
  val->kind = E_compoundstmt;
  val->compoundstmt.decllist = decllist;
  val->compoundstmt.stmtlist = stmtlist;
  return val;
}

T_stmtlist create_stmtlist(T_stmt stmt, T_stmtlist tail) {
  if (NULL == stmt) {
    fprintf(stderr, "FATAL: setting stmt in create_stmtlist to NULL!\n");
    exit(1);
  }
  T_stmtlist val = xmalloc(sizeof(*val));
  val->stmt = stmt;
  val->tail = tail;
  return val;
}

T_type create_primitivetype(E_typename primitivetype) {
  
  T_type val = xmalloc(sizeof(*val));
  val->kind = E_primitivetype;
  val->primitivetype = primitivetype;
  return val;
}

T_type create_pointertype(T_type pointertype) {
  if (NULL == pointertype) {
    fprintf(stderr, "FATAL: setting pointertype in create_pointertype to NULL!\n");
    exit(1);
  }
  T_type val = xmalloc(sizeof(*val));
  val->kind = E_pointertype;
  val->pointertype = pointertype;
  return val;
}

T_type create_arraytype(int size, T_type type) {
  if (NULL == type) {
    fprintf(stderr, "FATAL: setting type in create_arraytype to NULL!\n");
    exit(1);
  }
  T_type val = xmalloc(sizeof(*val));
  val->kind = E_arraytype;
  val->arraytype.size = size;
  val->arraytype.type = type;
  return val;
}

T_type create_functiontype(T_typelist paramtypes, T_type returntype) {
  if (NULL == returntype) {
    fprintf(stderr, "FATAL: setting returntype in create_functiontype to NULL!\n");
    exit(1);
  }
  T_type val = xmalloc(sizeof(*val));
  val->kind = E_functiontype;
  val->functiontype.paramtypes = paramtypes;
  val->functiontype.returntype = returntype;
  return val;
}

T_typelist create_typelist(T_type type, T_typelist tail) {
  if (NULL == type) {
    fprintf(stderr, "FATAL: setting type in create_typelist to NULL!\n");
    exit(1);
  }
  T_typelist val = xmalloc(sizeof(*val));
  val->type = type;
  val->tail = tail;
  return val;
}

T_decl create_decl(T_type type, string ident) {
  if (NULL == type) {
    fprintf(stderr, "FATAL: setting type in create_decl to NULL!\n");
    exit(1);
  }
  T_decl val = xmalloc(sizeof(*val));
  val->type = type;
  val->ident = ident;
  return val;
}

T_decllist create_decllist(T_decl decl, T_decllist tail) {
  if (NULL == decl) {
    fprintf(stderr, "FATAL: setting decl in create_decllist to NULL!\n");
    exit(1);
  }
  T_decllist val = xmalloc(sizeof(*val));
  val->decl = decl;
  val->tail = tail;
  return val;
}

T_paramlist create_paramlist(string ident, T_paramlist tail) {
  
  T_paramlist val = xmalloc(sizeof(*val));
  val->ident = ident;
  val->tail = tail;
  return val;
}

T_func create_func(string ident, T_paramlist paramlist, T_type type, T_decllist decllist, T_stmtlist stmtlist, T_expr returnexpr) {
  if (NULL == type) {
    fprintf(stderr, "FATAL: setting type in create_func to NULL!\n");
    exit(1);
  }
  if (NULL == returnexpr) {
    fprintf(stderr, "FATAL: setting returnexpr in create_func to NULL!\n");
    exit(1);
  }
  T_func val = xmalloc(sizeof(*val));
  val->ident = ident;
  val->paramlist = paramlist;
  val->type = type;
  val->decllist = decllist;
  val->stmtlist = stmtlist;
  val->returnexpr = returnexpr;
  return val;
}

T_funclist create_funclist(T_func func, T_funclist tail) {
  if (NULL == func) {
    fprintf(stderr, "FATAL: setting func in create_funclist to NULL!\n");
    exit(1);
  }
  T_funclist val = xmalloc(sizeof(*val));
  val->func = func;
  val->tail = tail;
  return val;
}

T_main create_main(T_decllist decllist, T_stmtlist stmtlist, T_expr returnexpr) {
  if (NULL == returnexpr) {
    fprintf(stderr, "FATAL: setting returnexpr in create_main to NULL!\n");
    exit(1);
  }
  T_main val = xmalloc(sizeof(*val));
  val->decllist = decllist;
  val->stmtlist = stmtlist;
  val->returnexpr = returnexpr;
  return val;
}

