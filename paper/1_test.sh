#!/bin/bash

# Config
# Max allowed running time
timeout=15
# Max allowed RAM (in GBytes)
maxram=8
ulimit -Sv $(( ${maxram} * 1024 * 1024 ))
# Program to test
bindir=$(readlink -f ../paper/)
bin=$(readlink -f ../bin/polytime-cpp)
test -x "$bin" || exit 1

inputdir=$(readlink -f ./input)
outputdir=$(readlink -f ./output)
okdir=$(readlink -f ./ok)

# End config

n="$1"
m=$(($2 * $n / 2))
rate="$3"
i="$4"




base=${n}_${m}_${rate}_${i}
okfile=ok_${n}_${m}_${rate}_${i}
nofile=no_${n}_${m}_${rate}_${i}

# Generate the instances
if [[ ( ! -f "$inputdir"/"$okfile"_M.txt ) && ( ! -f "$inputdir"/"$okfile"_M.txt.xz ) ]]
then 
    echo "generate instance: ${inputdir}/${okfile}_M.txt"
    touch "$inputdir"/"${okfile}"_M.txt
    cd ~/matrixgenerator/generate_persistent || exit 1
    ./generatePersistent.sh "$n" "$m" "$rate" "$okfile" > "$okfile".log
    mv "$okfile"* "$inputdir"/
    xz -9 "$inputdir"/"$okfile"_M.txt
fi
if [[ ( ! -f "$inputdir"/"$nofile"_M.txt ) && ( ! -f "$inputdir"/"$nofile"_M.txt.xz ) ]]
then 
    echo "generate instance: ${inputdir}/${nofile}_M.txt"
    touch "$inputdir"/"$nofile"_M.txt
    cd ~/matrixgenerator/generate_persistent || exit 1
    ./generatePersistent.sh -n "$n" "$m" "$rate" "$nofile"> "$nofile".log
    mv "$nofile"_M.txt "$inputdir"/
    xz -9 "$inputdir"/"$nofile"_M.txt
fi

# Generate skeletons
if [[ ( ! -f "$inputdir"/../skeletons-input/"$okfile"_M.txt ) && ( ! -f "$inputdir"/../skeletons-input/"$okfile"_M.txt.xz ) ]]
then 
    echo "generate skeleton: ${inputdir}/${okfile}_M.txt"
    touch "$inputdir"/../skeletons-input/"$okfile"_M.txt
    xzcat "$inputdir"/"$okfile"_M.txt.xz | "$bindir"/extract_skeleton > "$inputdir"/../skeletons-input/"$okfile"_M.txt
    xz -9 "$inputdir"/../skeletons-input/"$okfile"_M.txt
    rm -f "$inputdir"/../skeletons-input/"$okfile"_M.txt.ms "$inputdir"/"$okfile"_M.txt
fi
if [[ ( ! -f "$inputdir"/../skeletons-input/"$nofile"_M.txt ) && ( ! -f "$inputdir"/../skeletons-input/"$nofile"_M.txt.xz ) ]]
then 
    echo "generate skeleton: ${inputdir}/${nofile}_M.txt"
    touch "$inputdir"/../skeletons-input/"$nofile"_M.txt
    xzcat "$inputdir"/"$nofile"_M.txt.xz | "$bindir"/extract_skeleton > "$inputdir"/../skeletons-input/"$nofile"_M.txt
    xz -9 "$inputdir"/../skeletons-input/"$nofile"_M.txt
    rm -f "$inputdir"/../skeletons-input/"$nofile"_M.txt.ms "$inputdir"/"$nofile"_M.txt
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
        unxz -k "$infile".xz
        if [ ! -f "$infile" ]
        then
            echo "Missing $infile!"
            exit 2
        fi
        timecmd="/usr/bin/time -f \"%e\" -o $logfile /usr/bin/timeout -s 9 ${timeout}m"
        fullcmd="$timecmd $bin $infile 2>&1  $outfile"
	echo "Solving: $infile > $outfile" 
        eval "$fullcmd"
        xz -f "$outfile"
        rm -f "$infile"
    fi
done
# Solving skeletons
for type in ok no
do
    logfile="$outputdir"/../skeletons-output/"$type"_"$base".log
    outfile="$outputdir"/../skeletons-output/"$type"_"$base".out
    infile="$inputdir"/../skeletons-input/"$type"_"$base"_M.txt
    if [[ ( ! -f "$logfile" ) && ( ! -f "$logfile".xz ) ]]
    then
        touch "$logfile"
        unxz -k "$infile".xz
        if [ ! -f "$infile" ]
        then
            echo "Missing $infile!"
            exit 2
        fi
        timecmd="/usr/bin/time -f \"%e\" -o $logfile /usr/bin/timeout -s 9 ${timeout}m"
        fullcmd="$timecmd $bin $infile 2>&1  $outfile"
	echo "Solving: $infile > $outfile" 
        eval "$fullcmd"
        xz -f "$outfile"
        rm -f "$infile"
    fi
done
