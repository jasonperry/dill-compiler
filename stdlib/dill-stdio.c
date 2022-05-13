// low-level standard library functions for Dill

// TODO: a debug directive to build with debug info.

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <gc.h>

struct int_array {
  int64_t length;
  int64_t* data;
};

struct byte_array {
  int64_t length;
  char* data;
};

struct int_array initIntArray(int64_t length, int64_t value) {
  struct int_array a;
  a.length = length;
  a.data = GC_malloc(length * sizeof(int64_t));
  for (int i=0; i < length; i++)
    a.data[i] = value;
  return a;
}

void printInt(int64_t n) {
  printf("%ld\n", n);
  return;
}

void printFloat(double x) {
  printf("%f\n", x);
  return;
}

/*  // need to figure what to do with the LLVM i1. 
void printBool(int b) {
  printf("%s\n", b ? "True" : "False");
  return;
}
*/

void printBytes(struct byte_array ba) {
  fwrite(ba.data, 1, ba.length, stdout);
}

void printString(char* s) {
  puts(s);
  return;
}

/** Closest match to LLVM String? type. */
typedef struct {
  bool tag;
  char* s;
} nullstr;


/** Not working yet, maybe after change tag type to i8. */
nullstr getLineStdin() {
  char* s;
  size_t n = 0;
  nullstr result;
  result.s = NULL;
  ssize_t bytes_read = getline(&(result.s), &n, stdin);
  if (bytes_read == -1) {
    result.tag = 0;
  }
  // should check errno as well to be fully robust.
  else {
    // later, if Dill strings store their size, will need to set that.
    result.tag = 1;
  }
  return result;
}
  
