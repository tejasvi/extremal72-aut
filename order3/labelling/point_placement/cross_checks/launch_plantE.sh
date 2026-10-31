#!/bin/bash
# csp5p only: E-mode planted labellings (uniformly random, not in normal form) on 200 random codes
cd "$(dirname "$0")"
mkdir -p runs/plantE && cd runs/plantE
head -200 ../../inputs/rand1200.txt > plant200.txt
split -n l/20 -d -a 3 plant200.txt ch_
for f in ch_???; do ( PLANT=4242 COUNT=1 nice -n 10 ../../../prod_v1/csp5p 24 E $f ../../../prod_v1/octdod.txt > $f.csp 2>&1 ) & done
wait
echo ALLDONE > ALLDONE
