#!/bin/bash
# gen_starts_all.sh DMAX "CODES" : (box) candidate lists, then all flagbeam4 builds in parallel (xargs -P 150),
# then the scan job list <HOME>/struct/starts/jobs_b.txt
dm=$1; codes=$2; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/starts
for ci in $codes; do c7=$B/starts/y$ci.cands$dm; [ -s $c7 ] || nice -n 10 <HOME>/venv/bin/python -I $B/src/ginvstart.py $ci $dm > $c7 & done; wait
: > $B/starts/fb_jobs.txt
for ci in $codes; do c7=$B/starts/y$ci.cands$dm; n=$(wc -l < $c7)
  for K in $(seq 1 $n); do echo "$ci $K $(sed -n "${K}p" $c7 | awk '{print $NF}')" >> $B/starts/fb_jobs.txt; done; done
cat $B/starts/fb_jobs.txt | xargs -P 150 -L 1 sh -c 'f='"$B"'/starts/b$0_$1.flag; [ -s $f ] || { MAXL=1 nice -n 10 '"$B"'/src/flagbeam4 '"$B"'/inst/data/gen_$0.txt '"$B"'/inst/data/low_$0.txt 1000 "$2" 2> /dev/null | grep "^FLAG" > $f.tmp && mv $f.tmp $f; }'
awk '{print $1, "b"$1"_"$2, "'"$B"'/starts/b"$1"_"$2".flag"}' $B/starts/fb_jobs.txt > $B/starts/jobs_b.txt
echo "GEN DONE $(wc -l < $B/starts/jobs_b.txt) flags"
