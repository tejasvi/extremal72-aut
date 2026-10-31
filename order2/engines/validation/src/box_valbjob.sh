#!/bin/bash
# box_valbjob.sh KIND ARGS : one lwe11b validation job on the box
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; R=<HOME>/alg/explore/runs2; B=bin/lwe11b
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
ulimit -v 4000000
case $1 in
std) C=$2; SPL=$(grep '^SPLIT_LEVEL ' $R/$C/PLAN.txt | awk '{print $2}'); src/box_runpart.sh $B $C $SPL 200000 17 logs/valb/std/$C
  EXP=$(grep '^PROBE_LTS ' $R/$C/PLAN.txt | awk '{print $2}'); GOT=$(PROBES=20000 LTSHFILE=$R/$C/sym.ltsh nice -n 10 $B $R/$C/inst.txt | tail -1 | awk '{print $NF}')
  A=$(hsh logs/val/std/${C}_lwe8.log); Bh=$(hsh logs/valb/std/$C.log)
  echo "$C lwe8 $A lwe11b $Bh $([ $A = $Bh ] && echo IDENTICAL || echo DIFFER) probe $EXP $GOT $([ "$EXP" = "$GOT" ] && echo PROBE_OK || echo PROBE_MISMATCH) user_s $(cut -d' ' -f1 logs/valb/std/$C.time)" >> logs/valb/STD_SUMMARY.txt ;;
check) C=$2; O=logs/valb/check/$2_$3_$4_$5; LWE11CHECK=1 LTSHFILE=$R/$C/sym.ltsh nice -n 10 $B $R/$C/inst.txt $3 $4 $5 > $O.log 2> $O.err
  REF=logs/check/$2_$3_$4_$5.lwe10.log; [ -s $REF ] || REF=logs/val6/check/$2_$3_$4_$5.lwe10.log
  echo "$C $3 $4 $5 [$(tail -1 $O.err)] lwe11b $(hsh $O.log) lwe10 $(hsh $REF) $([ $(hsh $O.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/valb/CHECK_SUMMARY.txt ;;
force) T=$2; C=$3; O=logs/valb/force/${T}_$3_$6; LWE11CHECK=1 LTSHFILE=$R/$C/sym.ltsh nice -n 10 bin/b_$T $R/$C/inst.txt $4 $5 $6 > $O.log 2> $O.err
  REF=logs/force/lwe10_$3_$4_$5_$6.log
  echo "$T $C $4 $5 $6 [$(tail -1 $O.err)] $(hsh $O.log) lwe10 $(hsh $REF) $([ $(hsh $O.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/valb/FORCE_SUMMARY.txt ;;
prod) C=$2; src/box_runpart.sh $B $C $3 $4 $5 logs/valb/prod/${C}_p$5
  A=$(hsh logs/ref/${C}_p$5_lwe8.log); Bh=$(hsh logs/valb/prod/${C}_p$5.log)
  echo "${C}_p$5 lwe8 $A lwe11b $Bh $([ $A = $Bh ] && echo IDENTICAL || echo DIFFER) user_s $(cut -d' ' -f1 logs/valb/prod/${C}_p$5.time)" >> logs/valb/PROD_SUMMARY.txt ;;
pair) E=$2; C=$3; src/box_runpart.sh bin/$E $C $4 $5 $6 logs/valb/paired/${C}_p$6_$E
  echo "pair ${C}_p$6 $E $(hsh logs/valb/paired/${C}_p$6_$E.log) user_s $(cut -d' ' -f1 logs/valb/paired/${C}_p$6_$E.time)" >> logs/valb/PAIR_SUMMARY.txt ;;
esac
