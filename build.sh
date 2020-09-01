#!/bin/bash

dune exec ./dillc.exe $1 2> testout/dillout.ll
name=$(basename "$1" .dl)
clang -o testout/$name testout/dillout.ll pervasives.c
