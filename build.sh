#!/bin/bash

if dune exec ./dillc.exe "$1"
then
    name=$(basename "$1" .dl)
    mv -f $name.ll out/
    clang -o out/$name out/$name.ll pervasives.c
else
    echo "Compile failed."
fi
