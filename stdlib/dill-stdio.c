// functions always available in the top-level of dill.
// later, have a stdlib module that's always opened.

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

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
nullstr stdio_getLine() {
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
  
