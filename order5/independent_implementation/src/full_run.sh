#!/bin/bash
# full_run.sh S THREADS : process the depth-1 nodes with index = S (mod 2), for every K0, at THR = 16
cd "$(dirname "$0")/.."
S=$1; T=$2
for K in 0 1 2 3 4 5 6; do
  rm -f logs/full_k${K}_s${S}.sol
  SOLFILE=logs/full_k${K}_s${S}.sol OMP_NUM_THREADS=$T nice -n 10 /usr/bin/time -f 'USER %U SYS %S ELAPSED %e MAXRSS_KB %M' \
    src/search 16 $K mod 2 $S > logs/full_k${K}_s${S}.log 2>&1
done
touch logs/full_done_s${S}
