#!/bin/bash
# project: production-size validation of lwe11 (alg, binary 50e12b07) against lwe8 (149ce3f3) on the 60 seeded parts
# of logs/ref/PARTS.txt. Each (code, part) runs once per engine; outputs in out/; summary by compare.sh.
cd <HOME>/lwe11val && export TMPDIR=<HOME>/lwe11val/tmp && mkdir -p out tmp
grep -v '^#' PARTS.txt | while read code spl npart parts; do
  for p in $parts; do echo "$code $spl $npart $p"; done
done > jobs.txt
# lwe11 jobs first (fast), then lwe8 (slow); at most NPROC concurrent
NPROC=${1:-130}
{ while read code spl npart p; do echo "lwe11 $code $spl $npart $p"; done < jobs.txt; while read code spl npart p; do echo "lwe8 $code $spl $npart $p"; done < jobs.txt; } > alljobs.txt
cat alljobs.txt | xargs -P $NPROC -L 1 sh -c 'e=$0; c=$1; s=$2; n=$3; p=$4; f=out/${e}_${c}_${p}.log; [ -s $f ] && grep -q "^DONE" $f && exit 0; LTSHFILE=$c/sym.ltsh nice -n 10 ./$e $c/inst.txt $s $n $p > $f.tmp 2>&1 && mv $f.tmp $f'
echo ALLDONE
