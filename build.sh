#!/bin/bash

basedir=~/code/dill-compiler
incdir=$basedir/stdlib
# outdir=$basedir/out    # if fresh clone, don't forget to ~mkdir out~

if [ $# -lt 1 ]; then
    echo "Specify source files (last becomes executable)"
    exit
fi

set -x
flags=""

for arg in $@; do
    if [[ "$arg" = -* ]]; then
	flags="$flags $arg"
	echo "Flags set to: $flags"
    elif dillc.exe --debug $flags -I $incdir "$arg"; then
	name=$(basename "$arg" .dl)
	# mv -f "$name.o" $outdir/
	objfiles="$objfiles $name.o"
    else
	echo "Compile failed."
	exit
    fi
    exename=$name.exe
done

if clang -no-pie -lgc -o $exename $objfiles $incdir/stdio.ll
then
    echo "Successfully built $exename"
fi
