#!/bin/bash
# tune2.sh CI TAG FLAGFILE : (box) prefixes = first k vectors (k=2..5) of FLAGFILE; continuations {MAXL, total} x beam
# {1000, 3000}; scan each
ci=$1; tag=$2; ff=$3; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/var
W=($(grep '^FLAG' $ff | cut -d' ' -f2-))
for k in 2 3 4 5; do pre=$(echo ${W[@]:0:$k} | tr ' ' ',')
  for v in m1000 m3000 l1000 l3000; do f=$B/var/u${ci}_${tag}_k${k}_$v.flag; b=${v:1}
    if [ ${v:0:1} = m ]; then E="MAXL=1"; else E="XX=1"; fi
    [ -s $f ] || env $E nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $B/inst/data/low_$ci.txt $b "$pre" 2> /dev/null | grep "^FLAG" > $f
    $B/boxsrc/scan_box.sh $ci u${tag}_k${k}_$v $f 50000 &
  done; wait
done
