diffc=0
for file in *.ml
do
    camlp5o pr_o.cmo "$file" > formatted_"$file"
    if [ $? -eq 0 ]
    then
        diff formatted_"$file" "$file" >/dev/null 2>/dev/null
        diffc=$((diffc+$?))
        mv formatted_"$file" "$file"
    else
        rm formatted_"$file"
    fi
done
if [ $diffc -gt 0 ]
then
    echo "changed"
fi
