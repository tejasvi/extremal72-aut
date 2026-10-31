#!/bin/bash
# rglue worker pool (resumable).  usage: rg_run.sh WORKDIR NW
#   WORKDIR contains rglue_static and chunks/c_XXXX (E_B lines, each with its global index as a token id=<i>).
#   Each worker claims a chunk by an O_EXCL lock file locks/c_XXXX, runs rglue, writes out/c_XXXX.txt.gz + .txt.eb, marks done/c_XXXX.
#   Restart after interruption: remove stale locks of chunks without done marks (done by this script at start).
set -u
W=$(readlink -f "$1"); NW=$2
export TMPDIR=$W/tmp
mkdir -p $W/out $W/done $W/locks $W/tmp $W/log
if [ -f $W/run.pid ] && kill -0 "$(cat $W/run.pid)" 2>/dev/null; then echo "already running (pid $(cat $W/run.pid))"; exit 1; fi
echo $$ > $W/run.pid
for l in $W/locks/c_*; do [ -e "$l" ] || continue; b=$(basename $l); [ -e $W/done/$b ] || rm -f $l; done
worker() {
  for c in $W/chunks/c_????; do
    b=$(basename $c)
    [ -e $W/done/$b ] && continue
    ( set -o noclobber; echo $$ > $W/locks/$b ) 2>/dev/null || continue     # O_EXCL lock (uutils mkdir is racy)
    nice -n 10 $W/rglue_static 16 8 $c $W/out/$b.txt > $W/log/$b.log 2>&1
    rc=$?
    if [ $rc -eq 0 ] && gzip -f $W/out/$b.txt; then touch $W/done/$b; echo "$(date -u +%FT%TZ) $b ok" >> $W/progress.log
    else echo "$(date -u +%FT%TZ) $b FAILED rc=$rc" >> $W/progress.log; fi
  done
}
for i in $(seq 1 $NW); do worker & done
wait
n=$(ls $W/chunks | grep -c '^c_....$'); d=$(ls $W/done | wc -l)
[ "$n" = "$d" ] && touch $W/ALLDONE
echo "$(date -u +%FT%TZ) pool exit: $d/$n done" >> $W/progress.log
rm -f $W/run.pid
