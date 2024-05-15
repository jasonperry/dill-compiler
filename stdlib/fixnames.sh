#!/bin/bash

# This script is to fix up LLVM IR code files that have been compiled
# from C for use with dill, by prepending the module name to functions.

# usage: ./fixnames.sh <modulename>
#  it assumes the module and filename are the same and appends .ll.

# Does it do it for global variables too? I need to check.
# Is this all we need to do? 

if [ "$1" == "" ]; then
    libname=stdio
else
    libname=$1
fi

# cat dill-stdio.ll | sed 's/\(define dso_local .* @\)\([a-zA-z0-9_]\+\)\((.*\)$/\1"stdio::\2"\3/' > stdio-fix.ll

# for some reason this doesn't work anymore, doesn't match.
# sed "s/\(define dso_local .* @\)\([a-zA-Z0-9_]+\)(\(.*\)\$/\1\"$libname::\2\"\3/" dill-$libname.ll > $libname-fix.ll

# removing the end-of-line expression seemed to fix it.
sed "s/\(define dso_local .* @\)\([a-zA-Z0-9_]\+\)(/\1\"$libname::\2\"(/" dill-$libname.ll > $libname-fix.ll
