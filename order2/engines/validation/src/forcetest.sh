#!/bin/bash
# forcetest.sh BIN CODE SPL NPART PART : LWE11CHECK run of a forced-path test build vs lwe10 output on the same part
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp; mkdir -p logs/force
B=$1; C=$2; D=<HOME>/c72/explore/runs2/$C; O=logs/force/$(basename $B)_${C}_$5
LWE11CHECK=1 LTSHFILE=$D/sym.ltsh nice -n 10 $B $D/inst.txt $3 $4 $5 > $O.log 2> $O.err
R=logs/force/lwe10_${C}_$3_$4_$5.log; [ -s $R ] || LTSHFILE=$D/sym.ltsh nice -n 10 bin/lwe10 $D/inst.txt $3 $4 $5 > $R 2>&1
A=$(grep -E '^LEVEL|^DONE|^SOL' $O.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16); Rh=$(grep -E '^LEVEL|^DONE|^SOL' $R | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
echo "$(basename $B) $C $3 $4 $5 [$(tail -1 $O.err)] $A vs lwe10 $Rh $([ $A = $Rh ] && echo SAME || echo DIFF)" >> logs/force/SUMMARY.txt
