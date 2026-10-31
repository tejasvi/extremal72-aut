#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/.." && pwd)"; export KLEIN
# generate fixed-first level-wise instances for all 119 (skip existing)
cd $KLEIN/model
python3 -I -c "
import pickle; c=pickle.load(open('classes.pkl','rb'))
for ci,_,_,n in c:
    for ri in range(n): print(ci,ri)
" > lw_all_list.txt
cat lw_all_list.txt | xargs -P 16 -L 1 bash -c 'f=lwinst/lwf_$0_$1.txt; [ -s $f ] && exit 0; nice -n 10 python3 -I lwprep.py $0 $1 $f fixedfirst > lwinst/prepf_$0_$1.log 2>&1'
echo GEN_DONE
