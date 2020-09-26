#!/bin/bash

for sf in $@; do
    if dune exec ./dillc.exe "$sf"; then
	name=$(basename "$sf" .dl)
	mv -f "$name.ll" out/
	irfiles="$irfiles out/$name.ll"
    else
	echo "Compile failed."
	exit
    fi
done

# oh, last one on command line is automatically name!
if clang -o out/$name $irfiles pervasives.c
then
    echo "Successfully built executable out/$name"
fi

#if dune exec ./dillc.exe "$1"
#then
#    name=$(basename "$1" .dl)
#    mv -f $name.ll out/
#else
#    echo "Compile failed."
#fi
