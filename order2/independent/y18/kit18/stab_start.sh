#!/bin/bash
# stab_start.sh FROM TO: launch detached stab workers with ids FROM..TO (requeue nothing; use stab_requeue.sh after a
# preemption). At most 120 workers per call.
cd "$(dirname "$0")"
[ "$1" -ge 1 ] 2>/dev/null && [ "$1" -le "$2" ] && [ $(( $2 - $1 + 1 )) -le 120 ] || { echo "bad range (at most 120 workers)"; exit 1; }   # guard
mkdir -p tmp
for w in $(seq $1 $2); do setsid nohup ./stab_worker.sh $w > /dev/null 2>&1 < /dev/null & done
echo "started stab workers $1..$2 $(date -u)"
