#include <string.h>

#include "util.h"
#include "table.h"

/**
This hash table implementation is taken from Modern Compiler
Implementation by Andrew Appel.
 */

unsigned int hash(char *s0) {
  unsigned int h= 0;
  char *s;
  for (s = s0; *s; s++) {
    h = h * 65599 + *s;
  }
  return h;
}

struct bucket *Bucket(string key, void *binding, struct bucket *next) {
  struct bucket *b = xmalloc(sizeof(*b));
  b->key = key;
  b->binding = binding;
  b->next = next;
  return b;
}

T_table create_table() {
  T_table table = xmalloc(sizeof(struct bucket *) * SIZE);
  memset(table, 0, sizeof(struct bucket *) * SIZE);
  return table;
}

void destroy_table(T_table table) {
  free(table);
}

void insert(T_table table, string key, void *binding) {
  int index = hash(key) % SIZE;
  table[index] = Bucket(key, binding, table[index]);
}

void *lookup(T_table table, string key) {
  int index = hash(key) % SIZE;
  struct bucket *b;
  for (b = table[index]; b; b = b->next) {
    if (0 == strcmp(b->key, key)) {
      return b->binding;
    }
  }
  return NULL;
}

void pop(T_table table, string key) {
  int index = hash(key) % SIZE;
  table[index] = table[index]->next;
}
