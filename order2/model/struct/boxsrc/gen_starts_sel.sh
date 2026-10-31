#!/bin/bash
# gen_starts_sel.sh DMAX PERDIM "CODES" : (box) from existing candidate lists keep the top PERDIM by pruning L for
# each dim 1..DMAX, build their flags in parallel (xargs -P 150), write the scan job list starts/jobs_sel.txt
dm=$1; pd=$2; codes=$3; B=<HOME>/struct; export TMPDIR=$B/tmp
: > $B/starts/fb_sel.txt
for ci in $codes; do c7=$B/starts/y$ci.cands$dm
  awk '{print NR, $2, substr($4,3)+0}' $c7 | sort -k2,2n -k3,3gr | awk -v pd=$pd '{c[$2]++; if (c[$2]<=pd) print $1}' | sort -n | \
    awk -v ci=$ci -v f=$c7 'BEGIN{while ((getline l < f) > 0) {n++; L[n]=l}} {split(L[$1], a, " "); print ci, $1, a[length(a)]}' >> $B/starts/fb_sel.txt
done
cat $B/starts/fb_sel.txt | xargs -P 150 -L 1 sh -c 'f='"$B"'/starts/b$0_$1.flag; [ -s $f ] || { MAXL=1 nice -n 10 '"$B"'/src/flagbeam4 '"$B"'/inst/data/gen_$0.txt '"$B"'/inst/data/low_$0.txt 1000 "$2" 2> /dev/null | grep "^FLAG" > $f.tmp && mv $f.tmp $f; }'
awk '{print $1, "b"$1"_"$2, "'"$B"'/starts/b"$1"_"$2".flag"}' $B/starts/fb_sel.txt > $B/starts/jobs_sel.txt
echo "GEN DONE $(wc -l < $B/starts/jobs_sel.txt) flags"
