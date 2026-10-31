#!/bin/bash
# Y23 search: join mode below every X-representative. usage: run_join.sh NPROC
D=<HOME>/c72_indep/y23
export TMPDIR=$D/tmp
NPROC=$1
[ "$NPROC" -ge 1 ] 2>/dev/null && [ "$NPROC" -le 16 ] || { echo "NPROC must be 1..16"; exit 1; }   # guard against process explosions
mkdir -p $D/out/join
for ((ch=0; ch<NPROC; ch++)); do
  nice -n 10 $D/src/engine9 $D/out/sep_A2.eng join $D/out/xreps23.txt 36 70 104 $NPROC $ch > $D/out/join/j_$ch.txt 2> $D/out/join/j_$ch.err &
done
wait
echo JOIN_DRIVER_DONE > $D/out/join/driver_done.txt
