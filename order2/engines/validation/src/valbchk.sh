#!/bin/bash
# valbchk.sh BIN TAG: LWE11CHECK runs on three small parts, one at a time; compared with the lwe10 outputs in logs/check/
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp; R=<HOME>/c72/explore/runs2; B=$1; T=$2
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
for j in "y28 3 40000000 1795" "y17 3 20000000 5407" "y29 2 200000000 782"; do set -- $j; O=logs/valb/check/${T}_$1_$2_$3_$4
  ulimit -v 4000000; LWE11CHECK=1 LTSHFILE=$R/$1/sym.ltsh nice -n 10 timeout 900 $B $R/$1/inst.txt $2 $3 $4 > $O.log 2> $O.err
  REF=logs/check/$1_$2_$3_$4.lwe10.log
  echo "$T $1 $2 $3 $4 [$(tail -1 $O.err)] $(hsh $O.log) lwe10 $(hsh $REF) $([ $(hsh $O.log) = $(hsh $REF) ] && echo SAME || echo DIFF)" >> logs/valb/CHECK_SUMMARY.txt
done
