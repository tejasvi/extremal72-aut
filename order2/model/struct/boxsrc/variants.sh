#!/bin/bash
# variants.sh CI TAG PREFIX : (box) flag variants for one forced prefix: MAXL beam 1000/3000, lse objective beam 1000/3000;
# each scanned with scan_box.sh
ci=$1; tag=$2; pre=$3; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/var
for v in m1000 m3000 l1000 l3000; do f=$B/var/v${ci}_${tag}_$v.flag
  b=${v:1}; if [ ${v:0:1} = m ]; then E="MAXL=1"; else E=""; fi
  [ -s $f ] || env $E nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $B/inst/data/low_$ci.txt $b "$pre" 2> /dev/null | grep "^FLAG" > $f
  $B/boxsrc/scan_box.sh $ci v${tag}_$v $f 50000 &
done; wait
