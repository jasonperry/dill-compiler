#!/bin/bash

dune exec ./dillc.exe $1 2> out/dillout.ll
name=$(basename "$1" .dl)
clang -o out/$name out/dillout.ll pervasives.c
