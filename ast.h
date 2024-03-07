#ifndef AST_H
#define AST_H
#include <stdbool.h>
#include <assert.h>

#include "util.h"

typedef char* string;
typedef struct S_prog* T_prog;
typedef enum { E_typename_int, E_typename_char } E_typename;
typedef enum { E_op_ref, E_op_deref, E_op_plus, E_op_minus, E_op_not, E_op_times, E_op_divide, E_op_mod, E_op_eq, E_op_ne, E_op_lt, E_op_le, E_op_gt, E_op_ge, E_op_and, E_op_or } E_op;
typedef struct S_exprlist* T_exprlist;
typedef struct S_expr* T_expr;
typedef struct S_stmt* T_stmt;
typedef struct S_stmtlist* T_stmtlist;
typedef struct S_type* T_type;
typedef struct S_typelist* T_typelist;
typedef struct S_decl* T_decl;
typedef struct S_decllist* T_decllist;
typedef struct S_paramlist* T_paramlist;
typedef struct S_func* T_func;
typedef struct S_funclist* T_funclist;
typedef struct S_main* T_main;
struct S_prog {
  T_decllist decllist;
  T_funclist funclist;
  T_main main;
};

struct S_exprlist {
  T_expr expr;
  T_exprlist tail;
};

struct S_expr {
  enum { E_identexpr, E_callexpr, E_intexpr, E_charexpr, E_strexpr, E_arrayexpr, E_unaryexpr, E_binaryexpr, E_castexpr } kind;
  union {
    string identexpr;
    struct { string ident; T_exprlist args; } callexpr;
    int intexpr;
    char charexpr;
    string strexpr;
    struct { T_expr expr; T_expr index; } arrayexpr;
    struct { E_op op; T_expr expr; } unaryexpr;
    struct { T_expr left; E_op op; T_expr right; } binaryexpr;
    struct { T_type type; T_expr expr; } castexpr;
  };
  T_type type;  // used for the type-checking project
};

struct S_stmt {
  enum { E_assignstmt, E_ifstmt, E_ifelsestmt, E_whilestmt, E_compoundstmt } kind;
  union {
    struct { T_expr left; T_expr right; } assignstmt;
    struct { T_expr cond; T_stmt body; } ifstmt;
    struct { T_expr cond; T_stmt ifbranch; T_stmt elsebranch; } ifelsestmt;
    struct { T_expr cond; T_stmt body; } whilestmt;
    struct { T_decllist decllist; T_stmtlist stmtlist; } compoundstmt;
  };
};

struct S_stmtlist {
  T_stmt stmt;
  T_stmtlist tail;
};

struct S_type {
  enum { E_primitivetype, E_pointertype, E_arraytype, E_functiontype } kind;
  union {
    E_typename primitivetype;
    T_type pointertype;
    struct { int size; T_type type; } arraytype;
    struct { T_typelist paramtypes; T_type returntype; } functiontype;
  };
};

struct S_typelist {
  T_type type;
  T_typelist tail;
};

struct S_decl {
  T_type type;
  string ident;
};

struct S_decllist {
  T_decl decl;
  T_decllist tail;
};

struct S_paramlist {
  string ident;
  T_paramlist tail;
};

struct S_func {
  string ident;
  T_paramlist paramlist;
  T_type type;
  T_decllist decllist;
  T_stmtlist stmtlist;
  T_expr returnexpr;
};

struct S_funclist {
  T_func func;
  T_funclist tail;
};

struct S_main {
  T_decllist decllist;
  T_stmtlist stmtlist;
  T_expr returnexpr;
};

T_prog create_prog(T_decllist decllist, T_funclist funclist, T_main main);

T_exprlist create_exprlist(T_expr expr, T_exprlist tail);

T_expr create_identexpr(string identexpr);

T_expr create_callexpr(string ident, T_exprlist args);

T_expr create_intexpr(int intexpr);

T_expr create_charexpr(char charexpr);

T_expr create_strexpr(string strexpr);

T_expr create_arrayexpr(T_expr expr, T_expr index);

T_expr create_unaryexpr(E_op op, T_expr expr);

T_expr create_binaryexpr(T_expr left, E_op op, T_expr right);

T_expr create_castexpr(T_type type, T_expr expr);

T_stmt create_assignstmt(T_expr left, T_expr right);

T_stmt create_ifstmt(T_expr cond, T_stmt body);

T_stmt create_ifelsestmt(T_expr cond, T_stmt ifbranch, T_stmt elsebranch);

T_stmt create_whilestmt(T_expr cond, T_stmt body);

T_stmt create_compoundstmt(T_decllist decllist, T_stmtlist stmtlist);

T_stmtlist create_stmtlist(T_stmt stmt, T_stmtlist tail);

T_type create_primitivetype(E_typename primitivetype);

T_type create_pointertype(T_type pointertype);

T_type create_arraytype(int size, T_type type);

T_type create_functiontype(T_typelist paramtypes, T_type returntype);

T_typelist create_typelist(T_type type, T_typelist tail);

T_decl create_decl(T_type type, string ident);

T_decllist create_decllist(T_decl decl, T_decllist tail);

T_paramlist create_paramlist(string ident, T_paramlist tail);

T_func create_func(string ident, T_paramlist paramlist, T_type type, T_decllist decllist, T_stmtlist stmtlist, T_expr returnexpr);

T_funclist create_funclist(T_func func, T_funclist tail);

T_main create_main(T_decllist decllist, T_stmtlist stmtlist, T_expr returnexpr);


#endif
