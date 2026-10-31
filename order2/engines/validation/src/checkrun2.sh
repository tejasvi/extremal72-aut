#!/bin/bash
# checkrun.sh CODE SPL NPART PART : LWE11CHECK run of frozen/lwe11 vs a plain lwe10 run of the same part
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
CODE=$1; SPL=$2; NPART=$3; PART=$4; D=<HOME>/c72/explore/runs2/$CODE; O=logs/check2/${CODE}_${SPL}_${NPART}_${PART}
mkdir -p logs/check
LWE11CHECK=1 LTSHFILE=$D/sym.ltsh nice -n 10 frozen/lwe11 $D/inst.txt $SPL $NPART $PART > $O.chk.log 2> $O.chk.err
LTSHFILE=$D/sym.ltsh nice -n 10 bin/lwe10 $D/inst.txt $SPL $NPART $PART > $O.lwe10.log 2>&1
A=$(grep -E '^LEVEL|^DONE|^SOL' $O.chk.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
B=$(grep -E '^LEVEL|^DONE|^SOL' $O.lwe10.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
echo "$CODE $SPL $NPART $PART check:[$(tail -1 $O.chk.err)] lwe11=$A lwe10=$B $([ $A = $B ] && echo SAME || echo DIFF)" >> logs/check2/SUMMARY.txt
