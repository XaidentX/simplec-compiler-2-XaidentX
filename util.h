#ifndef UTIL_H
#define UTIL_H

#include <stdlib.h>
#include <malloc.h>

void todo(char *str);

void* xmalloc(size_t size);

int tointval(char *str, int base);
char tocharval(char *str);
char* tostrval(char *yytext);

#endif
