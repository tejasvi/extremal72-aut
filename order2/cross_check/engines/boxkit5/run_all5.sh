#!/bin/bash
# rc11 wave (bit-granular LTS): tasks5.txt with N workers.  Usage: run_all5.sh N
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
mkdir -p logs work tmp
sha256sum bin/* > logs/BIN.sha256
cat tasks5.txt | xargs -P ${1:-8} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE5
