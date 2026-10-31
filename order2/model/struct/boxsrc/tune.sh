#!/bin/bash
# tune.sh CI TAG PREFIX : (box) objective {MAXL, total} x beam {300, 1000, 3000} continuations of a forced prefix; scan
ci=$1; tag=$2; pre=$3; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/var
for v in m300 m1000 m3000 l300 l1000 l3000; do f=$B/var/t${ci}_${tag}_$v.flag; b=${v:1}
  if [ ${v:0:1} = m ]; then E="MAXL=1"; else E="XX=1"; fi
  [ -s $f ] || env $E nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $B/inst/data/low_$ci.txt $b "$pre" 2> /dev/null | grep "^FLAG" > $f
  $B/boxsrc/scan_box.sh $ci t${tag}_$v $f 50000 &
done; wait
