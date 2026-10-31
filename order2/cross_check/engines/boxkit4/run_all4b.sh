#!/bin/bash
# kit4 runner 2 (audit code, 2026-10-22): runs tasks4b.txt.  Starts a task only while all processes with a working
# directory under <HOME>/audit_c2 (both kits, this runner, the counting itself) number at most CAP (file CAP, default 32).
# Writes logs/ALLDONE4 when all its tasks have ended.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) -lname "$HOME/audit_c2*" 2>/dev/null | wc -l; }
while read -r line; do
  [ -z "$line" ] && continue
  while :; do CAP=$(cat CAP 2>/dev/null || echo 32); [ $(cnt) -le $CAP ] && break; sleep 15; done
  $KIT/runtask4b.sh $line < /dev/null > /dev/null 2>&1 &
  sleep 5
done < tasks4b.txt
wait
echo ALLDONE > logs/ALLDONE4
