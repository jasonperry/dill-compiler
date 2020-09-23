#!/bin/bash

if dune exec ./dillc.exe "$1"
then
    name=$(basename "$1" .dl)
    mv -f $name.ll out/
    if clang -o out/$name out/$name.ll pervasives.c
    then
	echo "Successfully built executable out/$name"
    fi
else
    echo "Compile failed."
fi
