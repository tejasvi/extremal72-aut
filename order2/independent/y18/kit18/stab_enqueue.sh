#!/bin/bash
# stab_enqueue.sh REP NSPLIT: queue Stab(X)-reduced split items for rep REP (hex). Needs stab/REP/stab.txt (from
# tools/stab_maps.py on stab/REP/rep.txt). Items: stabq/queue/REP.NSPLIT.SPLIT.
cd "$(dirname "$0")"
R=$1; N=$2
[ "$N" -ge 1 ] 2>/dev/null && [ "$N" -le 256 ] || { echo "NSPLIT must be 1..256"; exit 1; }   # guard
[ -s stab/$R/stab.txt ] && [ -s stab/$R/rep.txt ] || { echo "missing stab/$R/{rep,stab}.txt"; exit 1; }
mkdir -p stabq/queue stabq/running stabq/done
for k in $(seq 0 $((N - 1))); do
  it=$R.$N.$(printf %03d $k)
  [ -e stabq/queue/$it ] || [ -e stabq/done/$it ] || ls stabq/running/$it.* > /dev/null 2>&1 || : > stabq/queue/$it
done
echo "queued: $(ls stabq/queue | wc -l)"
