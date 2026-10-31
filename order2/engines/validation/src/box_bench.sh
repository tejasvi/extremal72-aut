#!/bin/bash
# box_bench.sh TAG : 3 copies each of lwe10_g14, lwe11b, lwe11b_native on the three bench parts, all at once
cd <HOME>/alg; mkdir -p logs/bench; TAG=$1
for j in "y29 2 2000000 782" "y28 3 400000 1795" "y17 3 400000 1777"; do set -- $j
  for k in 1 2 3; do for b in lwe10_g14 lwe11b lwe11b_native; do src/box_runpart.sh bin/$b $1 $2 $3 $4 logs/bench/${TAG}_$1_${b}_$k & done; done
done; wait; echo BENCH_DONE
