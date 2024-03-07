#include <malloc.h>
#include <stdio.h>
#include <string.h>

#include "util.h"

/*
 * This method is a placeholder for the unimplemented parts of the
 * compiler.  It gives an explicit message that part of the
 * implementation is left undone, and therefore cannot trust the
 * output for the given example.
 */
void todo(char *str) {
  fprintf(stdout, "TODO: %s\n", str);
}

/* malloc or die.  Adapted from busybox's xfuncs_printf.c */
void* xmalloc(size_t size) {
  void *ptr = malloc(size);
  if (ptr == NULL && size != 0) {
    fprintf(stderr, "FATAL: memory exhausted\n");
    exit(1);
  }
  return ptr;
}

/*
 * Turn a hex or decimal string constant into a C integer.  This will
 * terminate with an error if the constant is larger than a C integer.
 */
int tointval(char *str, int base) {
  char *endptr;
  /* printf("converting %s\n", str); */
  long int longval = strtol(str, &endptr, base);
  /* printf("done converting %s\n", str); */
  int intval = (int) longval;
  if (((long) intval) != longval) {
    printf("FATAL: constant too large for int: %s\n", str);
    exit(1);
  }
  return intval;
}

/*
 * Turn a character string into a C character.
 */
char tocharval(char *str) {
  if (strlen(str) > 3) { // enough for quotes and 1 characters
    printf("FATAL: constant too large for char: %s\n", str);
    exit(1);
  } else {
    // remove the quotes
    return str[1];
  }
  

  /* /\* https://stackoverflow.com/questions/3535023/convert-characters-in-a-c-string-to-their-escape-sequences *\/ */
  /* // failed xattempt to resolve C escape sequences */
  /* char buffer[16];   */
  /* if (strlen(str) > 4) { // enough for quotes and 2 characters */
  /*   printf("FATAL: constant too large for char: %s\n", str); */
  /*   exit(1); */
  /* } */
  /* printf("converting %s\n", str); */
  /* sprintf(&buffer, "%s", str); */
  /* if (strlen(str) > 3) { // enough for quotes and 2 characters */
  /*   printf("FATAL: converted constant too large for char: %s\n", str); */
  /*   exit(1); */
  /* } */
  /* if (strlen(buffer) < 3) { */
  /*   printf("FATAL: conversion of constant char failed: %s\n", str); */
  /*   exit(1); */
  /* } */
  /* // the character should be just after the first quote. */
  /* printf("after %s\n", buffer); */
  /* char charval = buffer[1]; */
  /* printf("result %c\n", charval); */
  /* return charval; */
}

/*
 * Make a copy of the lexer's text value, since it will use that
 * buffer for other things.
 */
char* tostrval(char *yytext) {
  size_t len = strlen(yytext);
  char *strval = xmalloc(sizeof(char *) * len + 1);  // add one for the end character
  strval = strncpy(strval, yytext, len);
  strval[len] = '\0';
  return strval;
}

