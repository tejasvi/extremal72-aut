#!/bin/bash
# sample-based cost estimates for K0 = 1..6
cd "$(dirname "$0")/.."
for k in 1 2 3 4 5 6; do
  OMP_NUM_THREADS=64 nice -n 10 /usr/bin/time -f 'USER %U ELAPSED %e' src/search 16 $k sample 256 7 > logs/sample_k$k.log 2>&1
done
