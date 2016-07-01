#!/bin/sh

rm results.txt
touch results.txt

for i in `ls  testfolder2`
do
    echo "$i"
    wc testfolder2/$i
    wc testfolder/$i
done

return 0
