#!/bin/bash
# box_pair20k.sh : per struct package, one part 10x larger than its samples (NPART/10, first sample part index mod NPART/10),
# lwe10_g14 and lwe11b3 started together; summary logs/pair20k/PAIRS.txt
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/pair20k
for P in struct/y*/; do d=$(basename $P); f=$(ls $P/samples/*.log | head -1); b=$(basename $f .log)
  SPL=$(echo $b | sed 's/^s\([0-9]*\)n.*/\1/'); NP=$(echo $b | sed 's/^s[0-9]*n\([0-9]*\)_p.*/\1/'); PT=$(echo $b | sed 's/.*_p//')
  NP2=$((NP / 10)); PT2=$((PT % NP2))
  for e in lwe10_g14 lwe11b3; do echo "$d $SPL $NP2 $PT2 $e"; done
done > logs/pair20k/jobs.txt
cat logs/pair20k/jobs.txt | xargs -P 56 -L 1 sh -c 'd=$0; spl=$1; np=$2; pt=$3; e=$4; P=<HOME>/alg/struct/$d; O=logs/pair20k/${d}_$e; ulimit -v 4000000
  LTSHFILE=$P/sym.ltsh /usr/bin/time -f "%U" -o $O.time nice -n 10 bin/$e $P/inst.txt $spl $np $pt > $O.log 2>&1
  echo "$d s${spl}n${np}_p$pt $e $(grep -E "^LEVEL|^DONE|^SOL" $O.log | sed "s/time [0-9]*s//" | sha256sum | cut -c1-16) user_s $(cat $O.time)" >> logs/pair20k/PAIRS.txt'
echo PAIR20K_DONE
