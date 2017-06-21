#!/bin/bash

RUNSOLVER="../../runsolver_src/runsolver"
EAHYPER="../../eahyper_src/eahyper.native"
SOLVER_DIR="../../LTL_SAT_solver"

stats=stats_$$
so=solver_out_$$
rso=runsolver_out_$$

TO=$1
shift

for (( i=0; i <= 16; i++ ))
do
    for (( j=0; j <= 16; j++ ))
    do
        for solver in $@
        do
            csv=hd_"$solver".csv
            if [ "$i" -eq "0" -a "$j" -eq "0" ]
            then
                echo "INSTANCE,STATE,WCTIME,CPUTIME,USERTIME,SYSTEMTIME,CPUUSAGE,MAXVM" > "$csv"
            fi
            echo -n "${i}->${j}," >> "$csv"
            echo "run $solver on hd $i -> hd $j ..."
            "$RUNSOLVER" -W "$TO" -v "$stats" -o "$so" -w "$rso" "$EAHYPER" -f <(./hd_gen -d "$i") -i <(./hd_gen -d "$j") --make-unique --"$solver" -d "$SOLVER_DIR" &>/dev/null
            cat "$so"|head -n 1
            if (grep -e '^Maximum wall clock time exceeded' "$rso" >/dev/null)
            then
                echo -n "2," >> "$csv"
            elif [ "$(wc -l "$so"|cut -d' ' -f1)" -eq "0" ]
            then
                echo -n "3," >> "$csv"
            elif [ "$(wc -l "$so"|cut -d' ' -f1)" -gt "1" ]
            then
                echo -n "3," >> "$csv"
            elif (grep -e '^does not imply' "$so" >/dev/null)
            then
                echo -n "0," >> "$csv"
            elif (grep -e '^does imply' "$so" >/dev/null)
            then
                echo -n "1," >> "$csv"
            else
                echo -n "3," >> "$csv"
            fi
            cat "$stats"|grep -v -e '^#'|sed -e 's/.*=//'|tr '\n' ','|sed -e 's/,$//' >> "$csv"
            echo >> "$csv"
        done
    done
done
if [ -f "$stats" ]
then
    rm "$stats" "$so" "$rso"
fi
