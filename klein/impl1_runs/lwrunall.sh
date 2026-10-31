#!/bin/bash
# level-wise engine on all 119 instances (unsplit; the six hard ones are already done with 64-way splits)
cd "$(dirname "$0")"
mkdir -p outall
ls lwinst/lwf_*.txt | sed 's#lwinst/lwf_##; s#\.txt##' | grep -v -x -E '21_2|3_6|23_2|20_7|15_2|25_2' > tasks_all.txt
cat tasks_all.txt | xargs -P ${1:-300} -L 1 bash -c 'f=outall/lw_$0.out; grep -q "^DONE lwe" $f 2>/dev/null && exit 0; nice -n 10 ./lwe lwinst/lwf_$0.txt > $f 2>&1'
echo ALLDONE > outall/ALLDONE
