#!/bin/bash
# beams.sh CI TAG PREFIX "BEAMS" : (box) MAXL flags for several beam widths with an optional forced prefix; scan each
ci=$1; tag=$2; pre=$3; beams=$4; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/var
for b in $beams; do f=$B/var/w${ci}_${tag}_$b.flag
  [ -s $f ] || MAXL=1 nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $B/inst/data/low_$ci.txt $b "$pre" 2> /dev/null | grep "^FLAG" > $f
  $B/boxsrc/scan_box.sh $ci w${tag}_$b $f 50000 &
done; wait
