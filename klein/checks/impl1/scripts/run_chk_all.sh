#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# independent check of all 119 local lwf instances, 4 parallel, nice 10
cd $KLEIN/checks/impl1
cat $KLEIN/model/lw_all_list.txt | xargs -P 4 -L 1 bash -c 'f=chk/chk_$0_$1.log; grep -q "^RESULT" $f 2>/dev/null && exit 0; nice -n 10 python3 -I scripts/indep_check.py $0 $1 $KLEIN/impl1_runs/lwinst/lwf_$0_$1.txt $KLEIN/impl1_runs/lwinst/lwf_$0_$1.txt.pkl chk/map_$0_$1.pkl > $f 2>&1'
echo CHK_ALL_DONE > chk/ALLDONE
