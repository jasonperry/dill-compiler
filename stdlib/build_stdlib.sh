#!/bin/bash

## combination of gen_ll and fixup, plus copy
set -x

function fixup
{
    if [ "$1" == "" ]; then
	libname=stdio
    else
	libname=$1
    fi

    # cat dill-stdio.ll | sed 's/\(define dso_local .* @\)\([a-zA-z0-9_]\+\)\((.*\)$/\1"stdio::\2"\3/' > stdio-fix.ll

    sed "s/\(define dso_local .* @\)\([a-zA-z0-9_]\+\)\((.*\)\$/\1\"$libname::\2\"\3/" dill-$libname.ll > $libname-fix.ll
}

clang -S -emit-llvm dill-stdio.c
fixup stdio
mv stdio.ll stdio-old.ll
mv stdio-fix.ll stdio.ll
