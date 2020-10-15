#!/bin/bash

exename=a.out
basedir=~/code/datlang
incdir=$basedir/stdlib
outdir=$basedir/out    # if fresh clone, don't forget to ~mkdir out~

for sf in $@; do
    if dillc.exe -I $incdir "$sf"; then
	name=$(basename "$sf" .dl)
	mv -f "$name.o" $outdir/
	objfiles="$objfiles $outdir/$name.o"
    else
	echo "Compile failed."
	exit
    fi
done

# last one on command line is automatically name?
if clang -o out/$exename $objfiles stdlib/stdio.ll
then
    echo "Successfully built executable out/$exename"
fi
