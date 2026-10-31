#!/bin/bash
# run_split.sh ENG REPFILE D0 D1 D2 NSPLIT TAG: NSPLIT detached joinsplit processes (nice 10, ulimit -v 1 GiB),
# output out/TAG/js_<k>.txt, stderr out/TAG/js_<k>.err, pids out/TAG/pids.txt
cd "$(dirname "$0")"
ENG=$1; REPS=$2; D0=$3; D1=$4; D2=$5; N=$6; TAG=$7
[ "$N" -ge 1 ] && [ "$N" -le 64 ] || { echo "NSPLIT must be 1..64"; exit 1; }
mkdir -p out/$TAG tmp
export TMPDIR=$PWD/tmp
: > out/$TAG/pids.txt
for k in $(seq 0 $((N - 1))); do
  ( ulimit -v 1048576; exec nice -n 10 ./engine11 $ENG joinsplit $REPS $D0 $D1 $D2 $N $k > out/$TAG/js_$k.txt 2> out/$TAG/js_$k.err ) < /dev/null &
  echo $! >> out/$TAG/pids.txt
done
echo "launched $N on $REPS tag $TAG at $(date -u)" | tee out/$TAG/info.txt
