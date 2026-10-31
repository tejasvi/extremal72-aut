#!/bin/bash
# box_tierc_x.sh : rc11 cross-check on struct's tier C lb packages (hostM, <CPU>): frozen lwe11b5 (<HOME>/alg/frz_b5/lwe11b,
# same decision code as rc11) with LTSHFILE=lb/sym.ltsh LTSBFILE=lb/sym.ltsb on lb/inst.txt, the same split/NPART/part as
# each of struct's 16 lwe10b logs per package; LEVEL/DONE/SOL/LBPRUNE must be identical. At most 16 processes.
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; O=logs/tierc; mkdir -p $O
for d in y0 y14 y19; do for f in <HOME>/struct/samples_lb/${d}_b/*.log; do echo "$d $(basename $f .log)"; done; done > $O/jobs.txt
cat $O/jobs.txt | xargs -P 16 -L 1 sh -c 'd=$0; b=$1; P=<HOME>/struct/runs/$d/lb; O=logs/tierc/${d}_$b; ulimit -v 4000000
  SPL=$(echo $b | sed "s/^s\([0-9]*\)n.*/\1/"); NP=$(echo $b | sed "s/^s[0-9]*n\([0-9]*\)_p.*/\1/"); PT=$(echo $b | sed "s/.*_p//")
  LTSHFILE=$P/sym.ltsh LTSBFILE=$P/sym.ltsb nice -n 10 frz_b5/lwe11b $P/inst.txt $SPL $NP $PT > $O.log 2> $O.err
  A=$(grep -E "^LEVEL|^DONE|^SOL|^LBPRUNE" <HOME>/struct/samples_lb/${d}_b/$b.log | sed "s/time [0-9]*s//" | sha256sum | cut -c1-16)
  B=$(grep -E "^LEVEL|^DONE|^SOL|^LBPRUNE" $O.log | sed "s/time [0-9]*s//" | sha256sum | cut -c1-16)
  echo "$d $b lwe10b $A lwe11b5 $B $([ $A = $B ] && echo IDENTICAL || echo DIFFER)" >> logs/tierc/SUMMARY.txt'
date -u > $O/DONE.txt
