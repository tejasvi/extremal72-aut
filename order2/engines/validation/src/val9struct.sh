#!/bin/bash
# val8struct.sh: rc9 on the first sample part of every struct package, one process at a time, vs the package's lwe10 sample
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
for P in <HOME>/c72/c2opt/struct/runs/y*/; do d=$(basename $P); [ -f $P/PLAN.txt ] || continue
  f=$(ls $P/samples/*.log | head -1); b=$(basename $f .log)
  SPL=$(echo $b | sed 's/^s\([0-9]*\)n.*/\1/'); NP=$(echo $b | sed 's/^s[0-9]*n\([0-9]*\)_p.*/\1/'); PT=$(echo $b | sed 's/.*_p//')
  ulimit -v 4000000; LTSHFILE=$P/sym.ltsh /usr/bin/time -f "%U" -o logs/val9/struct/${d}_$b.time nice -n 10 timeout 590 bin/lwe11rc9_dev $P/inst.txt $SPL $NP $PT > logs/val9/struct/${d}_$b.log 2>&1
  A=$(hsh $f); B=$(hsh logs/val9/struct/${d}_$b.log)
  echo "$d $b lwe10 $A rc9 $B $([ $A = $B ] && echo IDENTICAL || echo DIFFER) user_s lwe10_hostM $(awk '{print $2}' $P/samples/$b.time) rc8_local $(cat logs/val9/struct/${d}_$b.time)" >> logs/val9/STRUCT_SUMMARY.txt
done
echo STRUCT_DONE >> logs/val9/STRUCT_SUMMARY.txt
