#!/bin/bash
# usage: run_generic.sh PARITY NPART JOBS THREADS   (runs all (rep, part) with part%2==PARITY)
PAR=$1; NP=$2; J=$3; T=$4
cd "${WORKDIR:-.}"   # directory holding ./gen4; logs go to res/
mkdir -p res
for r in 0 1 2 3 4 5 6; do for p in $(seq 0 $((NP-1))); do
  if [ $((p % 2)) -eq $PAR ]; then echo "$r $p"; fi
done; done > jobs_$PAR.txt
cat jobs_$PAR.txt | xargs -P $J -L 1 bash -c 'r=$0; p=$1; f=res/r${r}_p${p}; if grep -q "TOTAL solutions" $f.err 2>/dev/null; then exit 0; fi; env OMP_NUM_THREADS='$T' NPART='$NP' PART=$p REP_ONLY=$r ./gen4 > $f.out 2> $f.err'
echo ALLDONE > res/done_$PAR
