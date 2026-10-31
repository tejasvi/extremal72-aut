#!/bin/bash
# gtest9 (c3class production core) on the same chunks / instances already run with csp5p and gtest4
cd "$(dirname "$0")"
G=$(pwd)/gt9src/gtest9
for S in rand1200 c3cls200 highbeta struct; do
  cd runs/$S
  for f in ch_???; do
    if [ "$S" = struct ] && [ "$f" = ch_000 ]; then continue; fi       # beta = 253 code: hours without symmetry
    ( nice -n 10 $G E $f > $f.gt9 2>&1 ) &
  done
  cd ../..
done
cd runs/pz
for sd in $(seq 11 60); do ( nice -n 10 $G P 0.285 $sd > P_$sd.gt9 2>&1 ) & done
for sd in $(seq 61 70); do ( nice -n 10 $G P 0.285 $sd 0.003 > P12_$sd.gt9 2>&1 ) & done
for spec in "0.01 1" "0.01 2" "0.01 3" "0.01 4" "0.01 5" "0.005 1" "0.005 2" "0.005 3" "0.004 6"; do set -- $spec; ( nice -n 10 $G Z $1 $2 > Z_$1_$2.gt9 2>&1 ) & done
wait
echo ALLDONE > ../GT9DONE
