#!/bin/bash
# rerun wide-instance tasks that were produced by the old 64-bit binary (birth time < SWAP_TIME) with the new binary
cd "$(dirname "$0")"
mkdir -p out2
grep '^OLD' wide_status.txt | awk '{print $2, $3}' > rerun_tasks.txt
cat rerun_tasks.txt | xargs -P ${1:-45} -L 1 bash -c 'f=out2/v4_$0_$1.out; if grep -q "^DONE result=COMPLETE" $f 2>/dev/null; then exit 0; fi; nice -n 10 ./v4gd4 inst/v4_$0.txt 14 search 1 5 16 $1 0 1 > $f 2> out2/v4_$0_$1.err'
echo ALLDONE > out2/ALLDONE
