#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# complete kill certificates for six small instances: every removed child of the whole search, 1 completion each
cd $KLEIN/checks/impl1
for i in 37_1 6_0 28_0 5_0 31_0 18_5; do echo $i; done | xargs -P 6 -I{} bash -c 'i={}; a=${i%_*}; b=${i#*_}; KCAP=1000000 nice -n 10 scripts/lwe_kill $KLEIN/impl1_runs/lwinst/lwf_$i.txt > killall/k_$i.txt 2>&1; nice -n 10 python3 -I scripts/witness.py $a $b $KLEIN/impl1_runs/lwinst/lwf_$i.txt $KLEIN/impl1_runs/lwinst/lwf_$i.txt.pkl chk/map_$i.pkl killall/k_$i.txt 1 $a$b > killall/w_$i.log 2>&1'
echo KILLALL_DONE > killall/ALLDONE
