#!/bin/bash

n="$1"
m=$(($2 * $n / 2))
rate="$3"
i="$4"
source ./generate_tests.conf

base=${n}_${m}_${rate}_${i}
okfile=ok_${n}_${m}_${rate}_${i}
nofile=no_${n}_${m}_${rate}_${i}

echo "New run: $n $m $rate $i"

# Generate the instances
if [ ! -f "$inputdir"/"$okfile"_M.txt ]
then 
	echo "generate instance: $okfile_M.txt"
    touch "$inputdir"/"$okfile"_M.txt
    rm -f "$outputdir"/ok_"$base".{log,out}
    cd ~/matrixgenerator/generate_persistent
    ./generatePersistent.sh $n $m $rate $okfile > "$okfile".log
    mv "$okfile"* "$inputdir"/
fi
if [ ! -f "$inputdir"/"$nofile"_M.txt ]
then 
	echo "generate instance: $nofile_M.txt"
    touch "$inputdir"/"$nofile"_M.txt
    rm -f "$outputdir"/no_"$base".{log,out}
    cd ~/matrixgenerator/generate_persistent
    ./generatePersistent.sh -n $n $m $rate $nofile> "$nofile".log
    mv "$nofile"_M.txt "$inputdir"/
fi

# Solving instances
for type in ok no
do
    logfile="$outputdir"/"$type"_"$base".log
    outfile="$outputdir"/"$type"_"$base".out
    infile="$inputdir"/"$type"_"$base"_M.txt
    if [[ ( ! -f "$logfile" ) && ( ! -f "$logfile".gz ) ]]
    then
        touch "$logfile"
        if [ ! -f "$infile" ]
        then
            echo "Missing $infile!"
            exit 2
        fi
        timecmd="/usr/bin/time -f \"%e\" -o $logfile /usr/bin/timeout -s 9 ${timeout}m"
        fullcmd="$timecmd $bin $infile > $outfile"
	echo "Solving: $infile > $outfile" 
        eval "$fullcmd"
        gzip -f9 "$outfile" "$logfile"
    fi
done
