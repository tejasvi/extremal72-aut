#!/bin/bash
# runlb.sh JOBFILE NPROC : (box) parts with the bit-granular prototype src/lwe10b (rebased instance + LTSH + LTSB in
# runs_lb/CODE/); lines 'CODE SPL NPART PART'; logs in samples_lb/CODE/p<PART>.log; skips finished parts
B=<HOME>/struct; export TMPDIR=$B/tmp
cat $1 | xargs -P $2 -L 1 sh -c 'c=$0; s=$1; n=$2; p=$3; d='"$B"'/samples_lb/$c; mkdir -p $d; f=$d/p$p.log
  if [ -s $f ] && grep -q "^DONE" $f; then exit 0; fi
  LTSHFILE='"$B"'/runs_lb/$c/g.ltsh LTSBFILE='"$B"'/runs_lb/$c/g.ltsb nice -n 10 /usr/bin/time -f "user %U" '"$B"'/src/lwe10b '"$B"'/runs_lb/$c/g.txt $s $n $p > $f.tmp 2>&1 && mv $f.tmp $f'
