#!/bin/bash
# hostM wave 2 (after logs/ALLDONE_g): lwe8 vs lwe11b vs lwe11b3 (frozen_b3 since 16:15, rebuilt here: 3eddc9a8).
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
while [ ! -f logs/ALLDONE_g ]; do sleep 60; done
export ENGSET="--eng lwe8=BIN/lwe8 --eng lwe11b=BIN/lwe11b --eng lwe11b3=$HOME/audit_c2/build_b3/lwe11b"
sha256sum bin/* $HOME/audit_c2/build_b3/lwe11b > logs/BIN2_g.sha256
cat tasks2.txt | xargs -P ${1:-7} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE2_g
