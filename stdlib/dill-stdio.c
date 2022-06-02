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

// This doesn't make it appear in the .ll
// FILE *fopen(const char *filename, const char *mode);

// it won't get named right anyway, so just use one
FILE* openFile(const char *filename, const char *mode) {
  FILE* result = fopen(filename, mode);
  if (result == NULL) {
    perror("Runtime error (openFile)");
    exit(1);
  }
  return result;
}

void closeFile(FILE** file) {
  fclose(*file);
}

// void pointer passed mutable results in the double-point.
struct byte_array readFile(FILE** fpp) {
  FILE* file = *fpp;
  // how to check if it's not open?
  fseek(file, 0L, SEEK_END);
  size_t length = ftell(file);
  fseek(file, 0L, SEEK_SET);
  struct byte_array result;
  result.length = length;
  result.data = GC_malloc(length);
  size_t bytesRead = fread(result.data, 1L, length, file);
  if (bytesRead != length) {
    fprintf(stderr,
	    "Runtime Error(readFile): tried to read %lu bytes, got %lu instead\n",
	    length, bytesRead);
    exit(1);
  }
  return result;
}
  
  

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
  
