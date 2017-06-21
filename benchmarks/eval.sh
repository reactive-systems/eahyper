#!/bin/bash
num_unsat=$(cat "$1"|cut -d, -f2|grep -e '^0'|wc -l)
num_sat=$(cat "$1"|cut -d, -f2|grep -e '^1'|wc -l)
num_to=$(cat "$1"|cut -d, -f2|grep -e '^2'|wc -l)
num_fail=$(cat "$1"|cut -d, -f2|grep -e '^3'|wc -l)
num_solved=$(( $num_unsat + $num_sat ))
if [ "$num_unsat" -gt "0" ]
then
    sum_unsat=$(cat "$1"|cut -d, -f2,3|grep -e '^0'|cut -d, -f2|tr '\n' '+'|sed -e 's/\(.\)/scale=4; \1/' -e "s/.$/x/"|tr 'x' '\n'|bc)
    avg_unsat=$(echo "scale=3; $sum_unsat/$num_unsat"|bc)
    avg_unsat=$(echo $avg_unsat|sed -e 's/^\./0./')
else
    sum_unsat="0.0"
    avg_unsat="-"
fi
if [ "$num_sat" -gt "0" ]
then
    sum_sat=$(cat "$1"|cut -d, -f2,3|grep -e '^1'|cut -d, -f2|tr '\n' '+'|sed -e 's/\(.\)/scale=4; \1/' -e "s/.$/x/"|tr 'x' '\n'|bc)
    avg_sat=$(echo "scale=3; $sum_sat / $num_sat"|bc)
    avg_sat=$(echo $avg_sat|sed -e 's/^\./0./')
else
    sum_sat="0.0"
    avg_sat="-"
fi
if [ "$num_solved" -gt "0" ]
then
    sum_solved=$(echo "scale=4; $sum_unsat + $sum_sat"|bc)
    avg_solved=$(echo "scale=3; $sum_solved/$num_solved"|bc)
    avg_solved=$(echo $avg_solved|sed -e 's/^\./0./')
else
    sum_solved="0.0"
    avg_solved="-"
fi
echo \#unsat,\#sat,\#timeouted,#failure,avg time unsat,avg time sat,\#solved,avg time solved
echo $num_unsat,$num_sat,$num_to,$num_fail,$avg_unsat,$avg_sat,$num_solved,$avg_solved
