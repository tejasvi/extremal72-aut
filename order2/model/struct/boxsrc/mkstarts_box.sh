#!/bin/bash
# mkstarts_box.sh CI DMAX MAXC : (box) all ginvstart candidates with dim <= DMAX (at most MAXC, by pruning L per dim),
# MAXL continuation by flagbeam4 (beam 1000) -> <HOME>/struct/starts/b{CI}_{K}.flag ; prints scan-job lines
ci=$1; dm=$2; mc=$3; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/starts
c7=$B/starts/y$ci.cands$dm
[ -s $c7 ] || nice -n 10 <HOME>/venv/bin/python -I $B/src/ginvstart.py $ci $dm > $c7
awk '{d=$2; L=substr($4,3)+0; print NR, d, L}' $c7 | sort -k3,3gr | head -$mc | while read K d L; do
  f=$B/starts/b${ci}_$K.flag
  if [ ! -s $f ]; then PRE=$(sed -n "${K}p" $c7 | awk '{print $NF}')
    MAXL=1 nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $B/inst/data/low_$ci.txt 1000 "$PRE" 2> /dev/null | grep "^FLAG" > $f.tmp && mv $f.tmp $f; fi
  echo "$ci b${ci}_$K $f"
done
