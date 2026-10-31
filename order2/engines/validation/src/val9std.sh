#!/bin/bash
# val7std.sh: rc9 on the 14 standard parts, ONE process at a time (main-VM rule), vs cached lwe8 outputs + probes
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
R=<HOME>/c72/explore/runs2; B=bin/lwe11rc9_dev
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
for C in y8 y4 y5b y22 y23 y5 y1 y1b y29 y28 y17 y17b y35 y18; do
  SPL=$(grep '^SPLIT_LEVEL ' $R/$C/PLAN.txt | awk '{print $2}')
  ulimit -v 4000000; src/runpart.sh $B $C $SPL 200000 17 logs/val9/std/${C}_rc9
  EXP=$(grep '^PROBE_LTS ' $R/$C/PLAN.txt | awk '{print $2}'); GOT=$(PROBES=20000 LTSHFILE=$R/$C/sym.ltsh nice -n 10 $B $R/$C/inst.txt | tail -1 | awk '{print $NF}')
  A=$(hsh logs/val/std/${C}_lwe8.log); Bh=$(hsh logs/val9/std/${C}_rc9.log)
  echo "$C lwe8 $A rc9 $Bh $([ $A = $Bh ] && echo IDENTICAL || echo DIFFER) probe $EXP $GOT $([ "$EXP" = "$GOT" ] && echo PROBE_OK || echo PROBE_MISMATCH) user_s $(cut -d' ' -f1 logs/val9/std/${C}_rc9.time)" >> logs/val9/STD_SUMMARY.txt
done
echo STD_DONE >> logs/val9/STD_SUMMARY.txt
