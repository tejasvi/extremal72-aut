#!/bin/bash
# bench3.sh TAG ROUNDS "CODE SPL NPART PART" BIN_A BIN_B : ROUNDS rounds, each round runs 3 copies of A and 3 of B at once
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
TAG=$1; R=$2; read CODE SPL NPART PART <<< "$3"; A=$4; B=$5
for r in $(seq 1 $R); do for k in 1 2 3; do for b in $A $B; do src/runpart.sh $b $CODE $SPL $NPART $PART logs/bench/${TAG}_$(basename $b)_r${r}k$k & done; done; wait; done
for b in $A $B; do
  ts=$(cat logs/bench/${TAG}_$(basename $b)_r*k*.time | cut -d' ' -f1 | sort -g | tr '\n' ' ')
  hs=$(for f in logs/bench/${TAG}_$(basename $b)_r*k*.log; do grep -E '^LEVEL|^DONE|^SOL' $f | sed 's/time [0-9]*s//' | sha256sum | cut -c1-12; done | sort -u | tr '\n' ' ')
  echo "$TAG $(basename $b): sorted user times [$ts] median $(echo $ts | tr ' ' '\n' | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}') hash $hs"
done
