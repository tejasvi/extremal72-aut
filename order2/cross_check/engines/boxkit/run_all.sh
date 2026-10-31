#!/bin/bash
# Run all tasks of tasks.txt with N parallel workers (nice 10); then signal ALLDONE.  Usage: run_all.sh N
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
mkdir -p logs work tmp
sha256sum bin/* scripts/naive scripts/lowwords > logs/BIN.sha256
cat tasks.txt | xargs -P ${1:-31} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE
