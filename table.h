#ifndef TABLE_H
#define TABLE_H

/**
This hash table implementation is taken from Modern Compiler
Implementation by Andrew Appel.
 */

typedef char* string;

struct bucket {
  string key;
  void *binding;
  struct bucket *next;
};

typedef struct bucket** T_table;

#define SIZE 109

T_table create_table();

void destroy_table(T_table table);

void insert(T_table table, string key, void *binding);

void *lookup(T_table table, string key);

#endif
