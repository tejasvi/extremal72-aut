#!/bin/bash
# Pass 2 (full DFS, canonical-kernel-word-first order of each class) on V-feasible canonical reps.
D=<HOME>/c72_indep/y8
export TMPDIR=$D/tmp
NPROC=$1
mkdir -p $D/out/p2
DATA=(y8_kc_993c0.eng y8_kc_1051270.eng y8_kc_441018160.eng)
for cls in 0 1 2; do
  F=$D/out/p1_feasible_c$cls.txt
  [ -s "$F" ] || continue
  for ((ch=0; ch<NPROC; ch++)); do
    nice -n 10 $D/src/engine8 $D/out/${DATA[$cls]} prefixes $F 40 $NPROC $ch > $D/out/p2/c${cls}_$ch.txt 2> $D/out/p2/c${cls}_$ch.err &
  done
  wait
done
echo PASS2_DRIVER_DONE > $D/out/p2/driver_done.txt
