#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# deep assignments (random descents to level L, random completions) -> e2e, for the 7 split instances
cd $KLEIN/checks/impl1
for c in "3_6 14" "15_2 14" "20_7 14" "23_2 14" "25_2 14" "21_2 13" "3_5 9"; do echo $c; done | xargs -P 6 -L 1 bash -c 'i=$0; L=$1; a=${i%_*}; b=${i#*_}; nice -n 10 python3 -I scripts/gen_deep.py $KLEIN/impl1_runs/lwinst/lwf_$i.txt $L 20 3 $a$b e2e/deep_$i.txt > e2e/deepgen_$i.log 2>&1; nice -n 10 python3 -I scripts/e2e.py $a $b $KLEIN/impl1_runs/lwinst/lwf_$i.txt $KLEIN/impl1_runs/lwinst/lwf_$i.txt.pkl chk/map_$i.pkl 0 1 --gauge --xfile e2e/deep_$i.txt > e2e/deep_$i.log 2>&1'
echo DEEP_DONE > e2e/ALLDONE_deep
