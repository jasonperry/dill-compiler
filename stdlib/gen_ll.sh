#!/bin/bash

clang -S -emit-llvm dill-stdio.c
# still have to fix up function names manually with stdio:: module prefix
