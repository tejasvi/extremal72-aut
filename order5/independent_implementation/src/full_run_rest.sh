#!/bin/bash
# full_run_rest.sh THREADS : K0 = 1..6, all depth-1 nodes, THR = 16
cd "$(dirname "$0")/.."
T=$1
for K in 1 2 3 4 5 6; do
  rm -f logs/full_k${K}_all.sol
  SOLFILE=logs/full_k${K}_all.sol OMP_NUM_THREADS=$T nice -n 10 /usr/bin/time -f 'USER %U SYS %S ELAPSED %e MAXRSS_KB %M' \
    src/search 16 $K all > logs/full_k${K}_all.log 2>&1
done
touch logs/full_done_rest
