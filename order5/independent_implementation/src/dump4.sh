#!/bin/bash
# rerun K0 = 0, 1 dumping every node of depth >= 4 (to inspect the 8 depth-4 nodes of the full run)
cd "$(dirname "$0")/.."
for K in 0 1; do
  DUMP=logs/dump4_k$K.txt DUMPD=6 DUMPMIN=4 SOLFILE=logs/dump4_k$K.sol OMP_NUM_THREADS=250 nice -n 10 src/search 16 $K all > logs/dump4_k$K.log 2>&1
done
touch logs/dump4_done
