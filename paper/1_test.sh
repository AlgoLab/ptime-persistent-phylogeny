#!/bin/bash

# Config
# Max allowed running time
timeout=15
# Max allowed RAM (in GBytes)
maxram=8
ulimit -Sv $(( ${maxram} * 1024 * 1024 ))
# Program to test
bin=$(readlink -f ../bin/polytime-cpp)
test -x "$bin" || exit 1

inputdir=./input
outputdir=./output
okdir=./ok

# End config

n="$1"
m=$(($2 * $n / 2))
rate="$3"
i="$4"




base=${n}_${m}_${rate}_${i}
okfile=ok_${n}_${m}_${rate}_${i}
nofile=no_${n}_${m}_${rate}_${i}

echo "New run: $n $m $rate $i"

# Generate the instances
if [[ ( ! -f "$inputdir"/"$okfile"_M.txt ) && ( ! -f "$inputdir"/"$okfile"_M.txt.xz ) ]]
then 
    echo "generate instance: ${okfile}_M.txt"
    touch "$inputdir"/"${okfile}"_M.txt
    rm -f "${outputdir}"/ok_"$base".{log,out}
    cd ~/matrixgenerator/generate_persistent || exit 1
    ./generatePersistent.sh "$n" "$m" "$rate" "$okfile" > "$okfile".log
    mv "$okfile"* "$inputdir"/
    xz -9 "$inputdir"/"$okfile"_M.txt
fi
if [[ ( ! -f "$inputdir"/"$nofile"_M.txt ) && ( ! -f "$inputdir"/"$nofile"_M.txt.xz ) ]]
then 
    echo "generate instance: ${nofile}_M.txt"
    touch "$inputdir"/"$nofile"_M.txt
    rm -f "$outputdir"/no_"$base".{log,out}
    cd ~/matrixgenerator/generate_persistent || exit 1
    ./generatePersistent.sh -n "$n" "$m" "$rate" "$nofile"> "$nofile".log
    mv "$nofile"_M.txt "$inputdir"/
    xz -9 "$inputdir"/"$nofile"_M.txt
fi

# Solving instances
for type in ok no
do
    logfile="$outputdir"/"$type"_"$base".log
    outfile="$outputdir"/"$type"_"$base".out
    infile="$inputdir"/"$type"_"$base"_M.txt
    if [[ ( ! -f "$logfile" ) && ( ! -f "$logfile".xz ) ]]
    then
        touch "$logfile"
        if [ ! -f "$infile" ]
        then
            unxz -k "$infile".xz
            echo "Missing $infile!"
            exit 2
        fi
        timecmd="/usr/bin/time -f \"%e\" -o $logfile /usr/bin/timeout -s 9 ${timeout}m"
        fullcmd="$timecmd $bin $infile > $outfile"
	echo "Solving: $infile > $outfile" 
        eval "$fullcmd"
        xz -9 "$outfile"
        rm -f "$infile"
    fi
done
