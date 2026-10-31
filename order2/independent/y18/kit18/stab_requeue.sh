#!/bin/bash
# stab_requeue.sh: after a preemption (no stab workers alive), move stabq/running/* back to the queue.
cd "$(dirname "$0")"
[ "$(ps -u $(id -u) -o args= | grep -c '^/bin/bash ./stab_worker.sh')" = "0" ] || { echo "stab workers alive"; exit 1; }
for f in stabq/running/*; do [ -e "$f" ] || continue; b=$(basename $f); mv "$f" "stabq/queue/${b%.*}"; done
echo "queue $(ls stabq/queue | wc -l)"
