#!/bin/bash
# valpgo.sh std CODE | check CODE SPL NPART PART : optional PGO build bin/lwe11rc5pgo vs cached lwe8 std outputs / CHECK mode
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
B=bin/lwe11rc5pgo; R=<HOME>/c72/explore/runs2
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
if [ $1 = std ]; then C=$2; SPL=$(grep '^SPLIT_LEVEL ' $R/$C/PLAN.txt | awk '{print $2}')
  src/runpart.sh $B $C $SPL 200000 17 logs/val5pgo/${C}_std
  EXP=$(grep '^PROBE_LTS ' $R/$C/PLAN.txt | awk '{print $2}'); GOT=$(PROBES=20000 LTSHFILE=$R/$C/sym.ltsh nice -n 10 $B $R/$C/inst.txt | tail -1 | awk '{print $NF}')
  echo "std $C lwe8 $(hsh logs/val/std/${C}_lwe8.log) pgo $(hsh logs/val5pgo/${C}_std.log) $([ $(hsh logs/val/std/${C}_lwe8.log) = $(hsh logs/val5pgo/${C}_std.log) ] && echo IDENTICAL || echo DIFFER) probe $EXP $GOT $([ "$EXP" = "$GOT" ] && echo PROBE_OK || echo PROBE_MISMATCH)" >> logs/val5pgo/SUMMARY.txt
else C=$2; O=logs/val5pgo/${C}_chk
  LWE11CHECK=1 LTSHFILE=$R/$C/sym.ltsh nice -n 10 $B $R/$C/inst.txt $3 $4 $5 > $O.log 2> $O.err
  REF=logs/check/${C}_$3_$4_$5.lwe10.log
  echo "check $C [$(tail -1 $O.err)] $(hsh $O.log) lwe10 $(hsh $REF) $([ $(hsh $O.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/val5pgo/SUMMARY.txt
fi
