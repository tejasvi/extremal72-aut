#!/bin/bash
# project: rerun of the Y29 rows of the engine gate after hostH's loss (20 seeded production parts; engines lwe8 = reference,
# rc7 645a9f5c, lwe11b 2fdae1bb, rc9 dfbad27a), on a fleet box. Outputs out/<eng>_y29_<part>.log; compare with compare3.sh.
cd <HOME>/lwe11val && export TMPDIR=<HOME>/lwe11val/tmp && mkdir -p out tmp
NP=${1:-24}
read code spl npart parts < PARTS_y29.txt
{ for p in $parts; do echo "lwe8 $code $spl $npart $p"; done; for e in rc7 l11b rc9; do for p in $parts; do echo "$e $code $spl $npart $p"; done; done; } > alljobs3.txt
cat alljobs3.txt | xargs -P $NP -L 1 sh -c 'e=$0; c=$1; s=$2; n=$3; p=$4; f=out/${e}_${c}_${p}.log; [ -s $f ] && grep -q "^DONE" $f && exit 0; ulimit -v 4000000; LTSHFILE=$c/sym.ltsh nice -n 10 ./$e $c/inst.txt $s $n $p > $f.tmp 2>&1 && mv $f.tmp $f'
echo ALLDONE3
