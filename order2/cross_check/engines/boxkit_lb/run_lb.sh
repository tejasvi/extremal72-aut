#!/bin/bash
# <CPU> LTSB wave runner (audit code, 2026-10-22): tasks_lb.txt.  Starts a task only while the processes with a working
# directory in this kit (runner, tasks, the counting itself) number at most CAP (file CAP_lb, default 6).
# Writes logs/ALLDONE_lb.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
mkdir -p logs work tmp
sha256sum bin/* scripts/* > logs/BIN.sha256
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) \( -lname "$KIT" -o -lname "$KIT/*" \) 2>/dev/null | wc -l; }
while read -r line; do
  [ -z "$line" ] && continue
  while :; do CAP=$(cat CAP_lb 2>/dev/null || echo 6); [ $(cnt) -le $CAP ] && break; sleep 15; done
  $KIT/runtask_lb.sh $line < /dev/null > /dev/null 2>&1 &
  sleep 5
done < tasks_lb.txt
wait
echo ALLDONE > logs/ALLDONE_lb
