#!/bin/bash
# hostM wave 2, runner 2 (audit code, 2026-10-22): lwe8 vs lwe11b vs lwe11b3 on tasks2b.txt (the wave 2 tasks not yet
# started, pins first, then parts in rounds).  Starts a task only while the processes with a working directory in this
# kit (runner, tasks, the counting itself) number at most CAP (file CAP_g, default 16).  Writes logs/ALLDONE2_g.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
export ENGSET="--eng lwe8=BIN/lwe8 --eng lwe11b=BIN/lwe11b --eng lwe11b3=$HOME/audit_c2/build_b3/lwe11b"
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) \( -lname "$KIT" -o -lname "$KIT/*" \) 2>/dev/null | wc -l; }
while read -r line; do
  [ -z "$line" ] && continue
  while :; do CAP=$(cat CAP_g 2>/dev/null || echo 16); [ $(cnt) -le $CAP ] && break; sleep 15; done
  $KIT/runtask_g2.sh $line < /dev/null > /dev/null 2>&1 &
  sleep 5
done < tasks2b.txt
wait
echo ALLDONE > logs/ALLDONE2_g
