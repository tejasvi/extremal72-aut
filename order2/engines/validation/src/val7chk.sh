#!/bin/bash
# val7chk.sh: LWE11CHECK runs of rc7 on three small parts, one at a time; compared with the lwe10 outputs in logs/check/
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp; R=<HOME>/c72/explore/runs2
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
for j in "y28 3 40000000 1795" "y17 3 20000000 5407" "y29 2 200000000 782"; do set -- $j; O=logs/val7/check/$1_$2_$3_$4
  ulimit -v 4000000; LWE11CHECK=1 LTSHFILE=$R/$1/sym.ltsh nice -n 10 timeout 900 bin/lwe11rc7 $R/$1/inst.txt $2 $3 $4 > $O.log 2> $O.err
  REF=logs/check/$1_$2_$3_$4.lwe10.log
  echo "$1 $2 $3 $4 [$(tail -1 $O.err)] rc7 $(hsh $O.log) lwe10 $(hsh $REF) $([ $(hsh $O.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/val7/CHECK_SUMMARY.txt
done
echo CHECK_DONE >> logs/val7/CHECK_SUMMARY.txt
