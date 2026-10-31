#!/bin/bash
# wave 3 (after logs/ALLDONE2): sat's production candidate y29_der_max7 (derived constraints), all engines.
KIT=$(cd "$(dirname "$0")" && pwd); cd $KIT
while [ ! -f logs/ALLDONE2 ]; do sleep 60; done
export EXTRA_ENG="--eng rc9=$KIT/bin/rc9 --eng lwe10=$KIT/bin/lwe10 --eng lwe11c=$KIT/bin/lwe11c"
cat tasks3.txt | xargs -P ${1:-31} -L 1 ./runtask.sh
echo ALLDONE > logs/ALLDONE3
