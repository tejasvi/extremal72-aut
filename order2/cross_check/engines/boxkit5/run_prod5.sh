#!/bin/bash
# kit5 production-size runner (audit code, 2026-10-22): tasks5p.txt (single parts of 1/64000, the production NPART, at the
# production split 3).  Starts a task only while the processes with a working directory under this kit (the small-part
# wave, this runner, its tasks, the counting itself) number at most CAP (file CAP, default 12).  Writes logs/ALLDONE5p.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) -lname "$KIT*" 2>/dev/null | wc -l; }
while read -r line; do
  [ -z "$line" ] && continue
  while :; do CAP=$(cat CAP 2>/dev/null || echo 12); [ $(cnt) -le $CAP ] && break; sleep 15; done
  $KIT/runtask.sh $line < /dev/null > /dev/null 2>&1 &
  sleep 5
done < tasks5p.txt
wait
echo ALLDONE > logs/ALLDONE5p
