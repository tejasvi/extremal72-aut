#!/bin/bash
# worker.sh WID: claims items queue/REP.NSPLIT.SPLIT by atomic mv to running/ITEM.WID and runs
# ENGINE sep_A2.eng joinstab rep_REP.txt 36 70 104 stab14.txt NSPLIT SPLIT (ENGINE = contents of file ENGINE);
# output out/ITEM.out (renamed from .tmp only if the run exits 0 with one complete JT line), then running -> done.
cd "$(dirname "$0")"
W=$1
export TMPDIR=$PWD/tmp
while true; do
  it=""
  for c in $(ls queue 2>/dev/null | sort); do
    if mv queue/$c running/$c.$W 2> /dev/null; then it=$c; break; fi
  done
  [ -z "$it" ] && break
  R=${it%%.*}; rest=${it#*.}; N=${rest%%.*}; K=$((10#${rest#*.}))
  ENG=$(cat ENGINE)
  ( ulimit -v 1048576; exec nice -n 10 ./$ENG sep_A2.eng joinstab rep_$R.txt 36 70 104 stab14.txt $N $K ) > out/$it.tmp 2> out/$it.err < /dev/null
  rc=$?
  if [ $rc -eq 0 ] && [ "$(awk '$1=="JT" && NF==16' out/$it.tmp | wc -l)" = "1" ]; then
    mv out/$it.tmp out/$it.out && mv running/$it.$W done/$it
  else
    echo "item $it failed rc=$rc" >> failed.txt; mv running/$it.$W queue/$it; sleep 60
  fi
done
echo "worker $W finished $(date -u)" >> workers.log
