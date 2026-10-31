#!/bin/bash
# add_workers.sh FROM TO: launch extra detached workers with ids FROM..TO (no requeue; use while workers run)
cd "$(dirname "$0")"
[ "$1" -ge 1 ] 2>/dev/null && [ "$1" -le "$2" ] && [ $(( $2 - $1 + 1 )) -le 120 ] || { echo "bad range (at most 120 workers)"; exit 1; }   # guard against process explosions
for w in $(seq $1 $2); do setsid nohup ./worker.sh $w > /dev/null 2>&1 < /dev/null & done
echo "added workers $1..$2 $(date -u)" | tee -a workers.log
