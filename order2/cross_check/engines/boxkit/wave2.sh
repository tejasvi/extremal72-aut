#!/bin/bash
# wave 2 (after wave 1 has written logs/ALLDONE): add rc9 (frozen 2026-10-21 14:20), lwe10 and explore's frozen4 lwe11.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
while [ ! -f logs/ALLDONE ]; do sleep 60; done
export EXTRA_ENG="--eng rc9=$KIT/bin/rc9 --eng lwe10=$KIT/bin/lwe10 --eng lwe11c=$KIT/bin/lwe11c"
sha256sum bin/* > logs/BIN2.sha256
cat tasks2.txt | xargs -P ${1:-31} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE2
