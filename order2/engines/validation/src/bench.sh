#!/bin/bash
# bench.sh TAG REPS "CODE SPL NPART PART" BIN1 BIN2 ... : run all binaries concurrently on the same part, REPS rounds;
# prints per-round user times and the median per binary, and checks the LEVEL/DONE hash of every run.
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
TAG=$1; REPS=$2; read CODE SPL NPART PART <<< "$3"; shift 3
mkdir -p logs/bench
for r in $(seq 1 $REPS); do
  for b in "$@"; do src/runpart.sh $b $CODE $SPL $NPART $PART logs/bench/${TAG}_$(basename $b)_r$r & done; wait
done
for b in "$@"; do
  ts=$(for r in $(seq 1 $REPS); do cut -d' ' -f1 logs/bench/${TAG}_$(basename $b)_r$r.time; done | tr '\n' ' ')
  hs=$(for r in $(seq 1 $REPS); do grep -E '^LEVEL|^DONE|^SOL' logs/bench/${TAG}_$(basename $b)_r$r.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-12; done | sort -u | tr '\n' ' ')
  med=$(echo $ts | tr ' ' '\n' | sort -g | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}')
  echo "$TAG $(basename $b): median $med  runs [$ts] hash $hs"
done
