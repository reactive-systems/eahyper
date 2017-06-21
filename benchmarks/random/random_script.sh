#!/bin/bash

RUNSOLVER="../../runsolver_src/runsolver"
EAHYPER="../../eahyper_src/eahyper.native"
SOLVER_DIR="../../LTL_SAT_solver"

stats=stats_$$
so=solver_out_$$
rso=runsolver_out_$$

TO=$1
FILEPATH="$2"
FILE=$(basename "$2")
shift
shift

for (( i=0; i <= 250; i++ ))
do
    for solver in $@
    do
        csv="${FILE}_${solver}.csv"
        if [ "$i" -eq "0" ]
        then
            echo "INSTANCE,STATE,WCTIME,CPUTIME,USERTIME,SYSTEMTIME,CPUUSAGE,MAXVM" > "$csv"
        else
            echo -n "$i," >> "$csv"
            echo "run $solver on $FILE formula #$i ..."
            "$RUNSOLVER" -W "$TO" -v "$stats" -o "$so" -w "$rso" "$EAHYPER" -m "$FILEPATH" -c $i --"$solver" -d "$SOLVER_DIR" &>/dev/null
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
            elif (grep -e '^ERROR: memory exhausted' "$so" >/dev/null)
            then
                echo -n "4," >> "$csv"
            elif (grep -e '^unsat' "$so" >/dev/null)
            then
                echo -n "0," >> "$csv"
            elif (grep -e '^sat' "$so" >/dev/null)
            then
                echo -n "1," >> "$csv"
            else
                echo -n "3," >> "$csv"
            fi
            cat "$stats"|grep -v -e '^#'|sed -e 's/.*=//'|tr '\n' ','|sed -e 's/,$//' >> "$csv"
            echo >> "$csv"
        fi
    done
done
if [ -f "$stats" ]
then
    rm "$stats" "$so" "$rso"
fi
