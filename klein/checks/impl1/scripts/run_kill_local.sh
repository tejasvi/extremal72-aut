#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# kill witnesses: lwe_kill on 4 random 1/4096 parts (SPL 4) of each split instance, then witness.py (3 completions)
cd $KLEIN/checks/impl1
{ for i in 3_6 15_2 20_7 23_2 25_2 21_2 3_5; do for p in 101 1234 2900 3777; do echo "$i $p"; done; done; } > kill/tasks.txt
cat kill/tasks.txt | xargs -P 6 -L 1 bash -c 'f=kill/k_$0_$1.txt; grep -q "^KILLED level 17" $f 2>/dev/null && exit 0; KCAP=100 KSEED=$1 nice -n 10 scripts/lwe_kill $KLEIN/impl1_runs/lwinst/lwf_$0.txt 4 4096 $1 > $f 2>&1'
for i in 3_6 15_2 20_7 23_2 25_2 21_2 3_5; do cat kill/k_${i}_*.txt | grep '^KILL ' > kill/all_$i.txt; done
ls kill/all_*.txt | sed 's#kill/all_##; s#\.txt##' | xargs -P 6 -I{} bash -c 'i={}; a=${i%_*}; b=${i#*_}; nice -n 10 python3 -I scripts/witness.py $a $b $KLEIN/impl1_runs/lwinst/lwf_$i.txt $KLEIN/impl1_runs/lwinst/lwf_$i.txt.pkl chk/map_$i.pkl kill/all_$i.txt 3 $a$b > kill/w_$i.log 2>&1'
echo KILL_DONE > kill/ALLDONE
