#!/bin/bash
# Pass 1 (V-block feasibility, vfirst order, depth 70) on the canonicalized class files, NPROC processes per class.
D=<HOME>/c72_indep/y8
export TMPDIR=$D/tmp
NPROC=$1
mkdir -p $D/out/p1
for cls in 0 1 2 other; do
  if [ "$cls" = other ]; then F=$D/out/canon8_other.txt; else F=$D/out/canon8_c$cls.txt; fi
  [ -s "$F" ] || continue
  for ((ch=0; ch<NPROC; ch++)); do
    nice -n 10 $D/src/engine8 $D/out/y8_vfirst.eng feas $F 40 70 - $NPROC $ch > $D/out/p1/c${cls}_$ch.txt 2> $D/out/p1/c${cls}_$ch.err &
  done
  wait
done
echo PASS1_DRIVER_DONE > $D/out/p1/driver_done.txt
