#!/bin/bash
# rc13/lwe11b7 wave runner (audit code, 2026-10-22): tasks6.txt.  Starts a task only while the processes with a working
# directory in this kit (runner, tasks, the counting itself) number at most CAP (file CAP, default 32).  Writes logs/ALLDONE6.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
mkdir -p logs work tmp
sha256sum bin/* scripts/* pkgs/*/* > logs/BIN.sha256
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) \( -lname "$KIT" -o -lname "$KIT/*" \) 2>/dev/null | wc -l; }
while read -r line; do
  [ -z "$line" ] && continue
  while :; do CAP=$(cat CAP 2>/dev/null || echo 32); [ $(cnt) -le $CAP ] && break; sleep 15; done
  $KIT/runtask6.sh $line < /dev/null > /dev/null 2>&1 &
  sleep 5
done < tasks6.txt
wait
echo ALLDONE > logs/ALLDONE6
