#!/bin/bash
# box_prefix.sh : per-part prefix time (levels <= split, NPART 1e12 so no part continues) of lwe10_g14 and lwe11b2 for
# every struct package, 2 engines x 28 packages, P parallel; summary logs/prefix/PREFIX.txt
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/prefix
for d in struct/y*/; do d=$(basename $d); spl=$(grep '^SPLIT_LEVEL' struct/$d/PLAN.txt | awk '{print $2}'); for e in lwe10_g14 lwe11b2; do echo "$d $spl $e"; done; done > logs/prefix/jobs.txt
cat logs/prefix/jobs.txt | xargs -P ${1:-40} -L 1 sh -c 'd=$0; spl=$1; e=$2; P=<HOME>/alg/struct/$d; ulimit -v 4000000; LTSHFILE=$P/sym.ltsh /usr/bin/time -f "%U" -o logs/prefix/${d}_$e.time nice -n 10 bin/$e $P/inst.txt $spl 1000000000000 999999999999 > logs/prefix/${d}_$e.log 2>&1; echo "$d $e prefix_user_s $(cat logs/prefix/${d}_$e.time)" >> logs/prefix/PREFIX.txt'
echo PREFIX_DONE
