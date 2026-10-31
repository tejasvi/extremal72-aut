#!/bin/bash
# hostM (<CPU>, AVX2 only): lwe8 vs lwe11b on tasks_g.txt with N workers.  Usage: run_all_g.sh N
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
mkdir -p logs work tmp
export ENGSET="--eng lwe8=BIN/lwe8 --eng lwe11b=BIN/lwe11b"
sha256sum bin/* scripts/naive scripts/lowwords > logs/BIN.sha256
cat tasks_g.txt | xargs -P ${1:-7} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE_g
