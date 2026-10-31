#!/bin/bash
# project: validation of the two PRODUCTION binaries, rc7 (645a9f5c, AVX-512) and lwe11b (2fdae1bb, AVX2), against
# lwe8 (149ce3f3) on the same 60 seeded parts as runval.sh. Outputs out/rc7_* and out/l11b_*; summary compare2.sh.
cd <HOME>/lwe11val && export TMPDIR=<HOME>/lwe11val/tmp && mkdir -p out tmp
NPROC=${1:-120}
{ while read code spl npart p; do echo "rc7 $code $spl $npart $p"; echo "l11b $code $spl $npart $p"; done < jobs.txt; } > alljobs2.txt
cat alljobs2.txt | xargs -P $NPROC -L 1 sh -c 'e=$0; c=$1; s=$2; n=$3; p=$4; f=out/${e}_${c}_${p}.log; [ -s $f ] && grep -q "^DONE" $f && exit 0; LTSHFILE=$c/sym.ltsh nice -n 10 ./$e $c/inst.txt $s $n $p > $f.tmp 2>&1 && mv $f.tmp $f'
echo ALLDONE2
