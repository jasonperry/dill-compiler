// functions always available in the top-level of dill.
// later, have a stdlib module that's always opened.

#include <stdio.h>

void printInt(int n) {
  printf("%d\n", n);
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
