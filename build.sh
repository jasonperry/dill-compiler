#!/bin/bash

if dune exec ./dillc.exe "$1"
then
    mv -f dillout.ll out/
    name=$(basename "$1" .dl)
    clang -o out/$name out/dillout.ll pervasives.c
else
    echo "Compile failed."
fi
