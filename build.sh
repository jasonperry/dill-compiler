#!/bin/bash

basedir=~/code/datlang
incdir=$basedir/stdlib
# outdir=$basedir/out    # if fresh clone, don't forget to ~mkdir out~

if [ $# -lt 1 ]; then
    echo "Specify source files (last becomes executable)"
    exit
fi

for sf in $@; do
    if dillc.exe --debug -I $incdir "$sf"; then
	name=$(basename "$sf" .dl)
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
