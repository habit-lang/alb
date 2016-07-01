#!/bin/sh

rm results.txt
touch results.txt

for i in `ls  *.out`
do
    echo "--------------------\n" >> results.txt
    echo "$i\n" >> results.txt
    time -v ./$i 2>> results.txt >> results.txt
done

return 0
