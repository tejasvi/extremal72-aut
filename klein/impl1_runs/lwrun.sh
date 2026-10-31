#!/bin/bash
# level-wise engine on the six hard C2xC2 instances, 64 parts each split at level 4
cd "$(dirname "$0")"
mkdir -p out
{ for i in 21_2 3_6 23_2 20_7 15_2 25_2; do for p in $(seq 0 63); do echo "$i $p"; done; done; } > tasks.txt
cat tasks.txt | xargs -P ${1:-340} -L 1 bash -c 'f=out/lw_$0_$1.out; grep -q "^DONE lwe" $f 2>/dev/null && exit 0; nice -n 10 ./lwe lwinst/lwf_$0.txt 4 64 $1 > $f 2>&1'
echo ALLDONE > out/ALLDONE
