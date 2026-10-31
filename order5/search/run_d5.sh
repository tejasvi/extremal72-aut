#!/bin/bash
cd "${WORKDIR:-.}"; mkdir -p d5   # directory holding ./gen4d5 and parts5.txt
cat parts5.txt | xargs -P 48 -L 1 bash -c 'r=$0; p=$1; f=d5/r${r}_p${p}; if grep -q "TOTAL solutions" $f.err 2>/dev/null; then exit 0; fi; env OMP_NUM_THREADS=8 NPART=32 PART=$p REP_ONLY=$r ./gen4d5 > $f.out 2> $f.err'
echo ALLDONE > d5/done
