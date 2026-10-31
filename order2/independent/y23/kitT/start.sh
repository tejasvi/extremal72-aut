#!/bin/bash
# start.sh NWORKERS: requeue running/* (from a previous start), launch NWORKERS detached workers
cd "$(dirname "$0")"
N=$1
[ "$N" -ge 1 ] && [ "$N" -le 120 ] || { echo "NWORKERS must be 1..120"; exit 1; }
mkdir -p queue running done out tmp
for f in running/*; do [ -e "$f" ] || continue; b=$(basename $f); mv "$f" "queue/${b%.*}"; done
for w in $(seq 1 $N); do setsid nohup ./worker.sh $w > /dev/null 2>&1 < /dev/null & done
echo "started $N workers $(date -u)" | tee -a workers.log
