#!/bin/bash
# kit4 runner 3 (audit code, 2026-10-22): runs TASKFILE (default tasks4c.txt).  Starts a task only while the processes
# with a working directory under this kit (runner, tasks, the counting itself) number at most CAP (file CAP, default
# 20).  Writes logs/ALLDONE4 when all its tasks have ended.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
TF=${1:-tasks4c.txt}
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) -lname "$KIT*" 2>/dev/null | wc -l; }
while read -r line; do
  [ -z "$line" ] && continue
  while :; do CAP=$(cat CAP 2>/dev/null || echo 20); [ $(cnt) -le $CAP ] && break; sleep 15; done
  $KIT/runtask4b.sh $line < /dev/null > /dev/null 2>&1 &
  sleep 5
done < $TF
wait
echo ALLDONE > logs/ALLDONE4
