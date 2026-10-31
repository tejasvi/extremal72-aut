#!/bin/bash
# stab_worker.sh WID: claims stabq/queue/REP.NSPLIT.SPLIT by atomic mv, runs engine15 joinstab on stab/REP/rep.txt with
# stab/REP/stab.txt; the output stab/REP/ITEM.out appears (renamed from .tmp) only after a run that exits 0 with one
# complete JT line. Exits when the queue is empty.
cd "$(dirname "$0")"
W=$1
export TMPDIR=$PWD/tmp
while true; do
  it=""
  for c in $(ls stabq/queue 2>/dev/null | sort); do
    if mv stabq/queue/$c stabq/running/$c.$W 2> /dev/null; then it=$c; break; fi
  done
  [ -z "$it" ] && break
  R=${it%%.*}; rest=${it#*.}; N=${rest%%.*}; K=$((10#${rest#*.}))
  ( ulimit -v 1048576; exec nice -n 10 ./engine15 sep_A2.eng joinstab stab/$R/rep.txt 36 70 104 stab/$R/stab.txt $N $K ) > stab/$R/$it.tmp 2> stab/$R/$it.err < /dev/null
  rc=$?
  if [ $rc -eq 0 ] && [ "$(awk '$1=="JT" && NF==16' stab/$R/$it.tmp | wc -l)" = "1" ]; then
    mv stab/$R/$it.tmp stab/$R/$it.out && mv stabq/running/$it.$W stabq/done/$it
  else
    echo "item $it failed rc=$rc" >> stabq/failed.txt; mv stabq/running/$it.$W stabq/queue/$it; sleep 60
  fi
done
