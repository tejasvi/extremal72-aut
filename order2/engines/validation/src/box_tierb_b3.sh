#!/bin/bash
# box_tierb_b3.sh : lwe11b3 on the 160 struct samples of the tier-B packages (y20 y20b y30 y32 y34) vs their lwe10
# outputs, at most 20 processes (hostM cap). Summary logs/tierb/SAMPLES.txt
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/tierb
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
for d in y20 y20b y30 y32 y34; do for f in struct/$d/samples/*.log; do echo "$d $(basename $f .log)"; done; done > logs/tierb/jobs.txt
cat logs/tierb/jobs.txt | xargs -P 20 -L 1 sh -c 'd=$0; b=$1; P=<HOME>/alg/struct/$d; O=logs/tierb/${d}_$b; ulimit -v 4000000
  SPL=$(echo $b | sed "s/^s\([0-9]*\)n.*/\1/"); NP=$(echo $b | sed "s/^s[0-9]*n\([0-9]*\)_p.*/\1/"); PT=$(echo $b | sed "s/.*_p//")
  LTSHFILE=$P/sym.ltsh /usr/bin/time -f "%U" -o $O.time nice -n 10 bin/lwe11b3 $P/inst.txt $SPL $NP $PT > $O.log 2> $O.err
  A=$(grep -E "^LEVEL|^DONE|^SOL" $P/samples/$b.log | sed "s/time [0-9]*s//" | sha256sum | cut -c1-16); B=$(grep -E "^LEVEL|^DONE|^SOL" $O.log | sed "s/time [0-9]*s//" | sha256sum | cut -c1-16)
  echo "$d $b lwe10 $A lwe11b3 $B $([ $A = $B ] && echo IDENTICAL || echo DIFFER) user_s $(cat $O.time)" >> logs/tierb/SAMPLES.txt'
date -u > logs/tierb/DONE.txt
