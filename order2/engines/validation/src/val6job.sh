#!/bin/bash
# val6job.sh KIND ARGS... : one rc6 validation job against the fixed binary bin/lwe11rc6 (logs in logs/val6/)
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
B=<HOME>/c72/c2opt/alg/bin/lwe11rc6; R=<HOME>/c72/explore/runs2
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
case $1 in
qr48) for a in "full qr prefix" "full alt prefix" "full qr late" "relaxed qr prefix"; do ENG=$B nice -n 10 <HOME>/c72/venv/bin/python -I -B src/qr48ctl_v6.py $a > "logs/val6/qr48/$(echo $a | tr ' ' _).log" 2>&1; done ;;
check) C=$2; SPL=$3; NP=$4; P=$5; O=logs/val6/check/${C}_${SPL}_${NP}_$P
  LWE11CHECK=1 LTSHFILE=$R/$C/sym.ltsh nice -n 10 $B $R/$C/inst.txt $SPL $NP $P > $O.chk.log 2> $O.chk.err
  REF=logs/check/${C}_${SPL}_${NP}_$P.lwe10.log; [ -s $REF ] || REF=logs/check2/${C}_${SPL}_${NP}_$P.lwe10.log
  [ -s $REF ] || { REF=logs/val6/check/${C}_${SPL}_${NP}_$P.lwe10.log; LTSHFILE=$R/$C/sym.ltsh nice -n 10 bin/lwe10 $R/$C/inst.txt $SPL $NP $P > $REF 2>&1; }
  echo "$C $SPL $NP $P [$(tail -1 $O.chk.err)] rc6 $(hsh $O.chk.log) lwe10 $(hsh $REF) $([ $(hsh $O.chk.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/val6/check/SUMMARY.txt ;;
std) C=$2; D=$R/$C; SPL=$(grep '^SPLIT_LEVEL ' $D/PLAN.txt | awk '{print $2}')
  while ! { [ -s logs/val/std/${C}_lwe8.log ] && grep -q '^DONE' logs/val/std/${C}_lwe8.log; }; do sleep 60; done
  src/runpart.sh $B $C $SPL 200000 17 logs/val6/std/${C}_rc6
  EXP=$(grep '^PROBE_LTS ' $D/PLAN.txt | awk '{print $2}'); GOT=$(PROBES=20000 LTSHFILE=$D/sym.ltsh nice -n 10 $B $D/inst.txt | tail -1 | awk '{print $NF}')
  A=$(hsh logs/val/std/${C}_lwe8.log); Bh=$(hsh logs/val6/std/${C}_rc6.log)
  echo "$C spl $SPL part 17/200000 lwe8 $A rc6 $Bh $([ $A = $Bh ] && echo IDENTICAL || echo DIFFER) probe plan $EXP rc6 $GOT $([ "$EXP" = "$GOT" ] && echo PROBE_OK || echo PROBE_MISMATCH) user_s lwe8 $(cut -d' ' -f1 logs/val/std/${C}_lwe8.time) rc6 $(cut -d' ' -f1 logs/val6/std/${C}_rc6.time)" >> logs/val6/std/SUMMARY.txt ;;
force) T=$2; C=$3; SPL=$4; NP=$5; P=$6; O=logs/val6/force/${T}_${C}_$P
  LWE11CHECK=1 LTSHFILE=$R/$C/sym.ltsh nice -n 10 bin/r6$T $R/$C/inst.txt $SPL $NP $P > $O.log 2> $O.err
  REF=logs/force/lwe10_${C}_${SPL}_${NP}_$P.log
  echo "$T $C $SPL $NP $P [$(tail -1 $O.err)] $(hsh $O.log) lwe10 $(hsh $REF) $([ $(hsh $O.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/val6/force/SUMMARY.txt ;;
esac
