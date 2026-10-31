#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# e2e on all 119 instances: 20 random assignments each, with gauge comparison; 4 parallel, nice 10
cd $KLEIN/checks/impl1
cat $KLEIN/model/lw_all_list.txt | xargs -P 4 -L 1 bash -c 'f=e2e/rand_$0_$1.log; grep -q "^RESULT" $f 2>/dev/null && exit 0; nice -n 10 python3 -I scripts/e2e.py $0 $1 $KLEIN/impl1_runs/lwinst/lwf_$0_$1.txt $KLEIN/impl1_runs/lwinst/lwf_$0_$1.txt.pkl chk/map_$0_$1.pkl 20 $0$1 --gauge > $f 2>&1'
echo E2E_ALL_DONE > e2e/ALLDONE_rand
