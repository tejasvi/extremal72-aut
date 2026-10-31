#!/bin/bash
# stab_topup.sh CAP [MAXLOAD]: box-side controller. Every 60 s: if the stab queue is not empty and my engine15 process
# count (queue workers + stab workers) is below CAP, start stab workers for the free slots (ids from stabq/next_id);
# with MAXLOAD, start at most MAXLOAD - (1-min load average) workers per cycle (ramp up on a shared box).
# Exits when the stab queue is empty. Log: stabq/topup.log
cd "$(dirname "$0")"
CAP=$1; ML=${2:-0}
[ "$CAP" -ge 1 ] 2>/dev/null && [ "$CAP" -le 380 ] || { echo "CAP must be 1..380"; exit 1; }   # guard
[ "$ML" -ge 0 ] 2>/dev/null && [ "$ML" -le 384 ] || { echo "MAXLOAD must be 0..384"; exit 1; }
mkdir -p stabq tmp
[ -e stabq/next_id ] || echo 1000 > stabq/next_id
while true; do
  q=$(ls stabq/queue 2>/dev/null | wc -l)
  [ "$q" -eq 0 ] && { echo "$(date -u) stab queue empty, exit" >> stabq/topup.log; exit 0; }
  n=$(ps -u $(id -u) -o args= | grep -c '^./engine15 ')
  f=$((CAP - n)); [ $f -gt $q ] && f=$q
  if [ "$ML" -gt 0 ]; then l=$(cut -d" " -f1 /proc/loadavg | cut -d. -f1); g=$((ML - l)); [ $g -lt 0 ] && g=0; [ $f -gt $g ] && f=$g; fi
  if [ $f -gt 0 ]; then
    a=$(cat stabq/next_id)
    for w in $(seq $a $((a + f - 1))); do setsid nohup ./stab_worker.sh $w > /dev/null 2>&1 < /dev/null & done
    echo $((a + f)) > stabq/next_id
    echo "$(date -u) queue $q engines $n: started $f stab workers ($a..$((a + f - 1)))" >> stabq/topup.log
  fi
  sleep 60
done
