#!/bin/bash

DIRNAME="$(dirname "$2")"
BASENAME="$(basename "$2")"
TO=$1
shift
shift

for file in $(echo "${DIRNAME}/${BASENAME}/"*)
do
    echo "eval $file ..."
    ./random_script.sh "$TO" "$file" $@
done

