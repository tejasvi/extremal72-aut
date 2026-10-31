#!/bin/bash
# rc9-focused wave: lwe8 vs rc9 vs lwe11b3 on tasks4.txt with N workers (each worker = 1 python + at most 1 engine).
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
mkdir -p logs work tmp
sha256sum bin/* scripts/naive scripts/lowwords > logs/BIN.sha256
cat tasks4.txt | xargs -P ${1:-16} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE4
