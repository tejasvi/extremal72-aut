#!/bin/bash
# gen_scan_all.sh DMAX NPROC "CODES" : (box) ALL ginvstart candidates (dim <= DMAX) of the codes: build the flag
# (flagbeam4 MAXL continuation) and scan it (scan_box.sh: raw probe + checkability model), NPROC jobs at a time; resumable
dm=$1; np=$2; codes=$3; B=<HOME>/struct; export TMPDIR=$B/tmp
: > $B/starts/all_jobs.txt
for ci in $codes; do c7=$B/starts/y$ci.cands$dm
  awk -v ci=$ci '{print ci, NR, $NF}' $c7 >> $B/starts/all_jobs.txt; done
cat $B/starts/all_jobs.txt | xargs -P $np -L 1 sh -c 'f='"$B"'/starts/b$0_$1.flag
  [ -s $f ] || { MAXL=1 nice -n 10 '"$B"'/src/flagbeam4 '"$B"'/inst/data/gen_$0.txt '"$B"'/inst/data/low_$0.txt 1000 "$2" 2> /dev/null | grep "^FLAG" > $f.tmp && mv $f.tmp $f; }
  [ -s $f ] && '"$B"'/boxsrc/scan_box.sh $0 b$0_$1 $f 50000'
echo "GENSCAN DONE $(wc -l < $B/starts/all_jobs.txt)"
