#include <stdio.h>

#include "ast.h"

#include "ast_printer.h"

#include "typecheck.h"

extern int yyparse (void);  // the entrypoint to the parser

extern FILE *yyout;  // the output of flex

extern T_prog program_ast;  // the output of bison

int main(int argc, char **argv) {
  /* while (1) { */
  /*   yylex(); */
  /* } */

  // print input program and parse errors to stderr
  yyout = stderr;

  // kick off the parser, which will store the result in program_ast
  yyparse();

  // type check the ast, which updates symbtab and annotates the tree
  check_prog(program_ast);

  // print the ast
  print_prog(program_ast, 0);
}
