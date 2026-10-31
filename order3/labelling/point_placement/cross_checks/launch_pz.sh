#!/bin/bash
# planted (P) and sextet (Z) instances with both programs; E-mode PLANT instances with csp5p only
cd "$(dirname "$0")"
mkdir -p runs/pz && cd runs/pz
G=../../gt4src/gtest4; C=../../../prod_v1/csp5p; B=../../../prod_v1/octdod.txt
for sd in $(seq 11 60); do
  ( nice -n 10 $G P 0.285 $sd > P_$sd.gt4 2>&1 ) &
  ( COUNT=1 nice -n 10 $C 24 P 0.285 $sd $B > P_$sd.csp 2>&1 ) &
done
for sd in $(seq 61 70); do
  ( nice -n 10 $G P 0.285 $sd 0.003 > P12_$sd.gt4 2>&1 ) &
  ( COUNT=1 nice -n 10 $C 24 P 0.285 $sd $B 0.003 > P12_$sd.csp 2>&1 ) &
done
for spec in "0.01 1" "0.01 2" "0.01 3" "0.01 4" "0.01 5" "0.005 1" "0.005 2" "0.005 3" "0.004 6"; do
  set -- $spec
  ( nice -n 10 $G Z $1 $2 > Z_$1_$2.gt4 2>&1 ) &
  ( COUNT=1 nice -n 10 $C 24 Z $1 $2 $B > Z_$1_$2.csp 2>&1 ) &
done
wait
echo ALLDONE > ALLDONE
