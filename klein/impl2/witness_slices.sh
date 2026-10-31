#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/.." && pwd)"; export KLEIN
# Extra witness sampling on further split slices of the 5 hard instances (production orders).
cd $KLEIN/impl2
for n in c04_b5 c16_b0 c21_b7 c24_b2 c26_b2; do
  for j in 31 63; do
    ( V4_WITNESS=200003 V4_WITNESS_MAX=60 nice -n 10 ./search_v4 inst2/i72_$n.txt 64 $j 9 > logs/w3_${n}_j$j.out 2>/dev/null
      nice -n 10 python3 -I verify_kills.py inst2/i72_$n.json inst2/i72_$n.txt logs/w3_${n}_j$j.out > logs/w3_${n}_j$j.json 2>&1 ) &
  done
done
wait
echo ALLDONE > logs/w3.done
