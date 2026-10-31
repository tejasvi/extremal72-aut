#!/bin/bash
# box_structjob.sh sample|check PKG sSPLnNPART_pPART
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; ulimit -v 4000000
K=$1; D=$2; B=$3; P=<HOME>/alg/struct/$D
SPL=$(echo $B | sed 's/^s\([0-9]*\)n.*/\1/'); NP=$(echo $B | sed 's/^s[0-9]*n\([0-9]*\)_p.*/\1/'); PT=$(echo $B | sed 's/.*_p//')
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
O=logs/struct3/${D}_$B
if [ $K = sample ]; then
  [ -s $O.log ] && grep -q '^DONE' $O.log || LTSHFILE=$P/sym.ltsh /usr/bin/time -f "%U %e %M" -o $O.time nice -n 10 bin/lwe11b3 $P/inst.txt $SPL $NP $PT > $O.log 2> $O.err
  A=$(hsh $P/samples/$B.log); Bh=$(hsh $O.log); t10=$(awk '{print $2}' $P/samples/$B.time); t11=$(cut -d' ' -f1 $O.time)
  echo "$D $B lwe10 $A lwe11b3 $Bh $([ $A = $Bh ] && echo IDENTICAL || echo DIFFER) user_s lwe10 $t10 lwe11b3 $t11" >> logs/struct3/SAMPLES.txt
else
  NP2=$((NP * 20)); LWE11CHECK=1 LTSHFILE=$P/sym.ltsh nice -n 10 timeout 3600 bin/lwe11b3 $P/inst.txt $SPL $NP2 $PT > ${O}_chk.log 2> ${O}_chk.err
  echo "$D s${SPL}n${NP2}_p$PT [$(tail -1 ${O}_chk.err)] $(grep -c '^DONE' ${O}_chk.log)" >> logs/struct3/CHECKS.txt
fi
