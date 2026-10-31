#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# usage: run_pinned.sh INST SOLVER SEED0 NTESTS NFIX NPLANT RELAX FLIPS
B=$1; SOLV=$2; S0=$3; NT=$4; NFIX=$5; NPL=$6; RLX=$7; FL=$8
D=$KLEIN/checks/gd/pinned; mkdir -p $D
PY=python3; SC=$KLEIN/checks/gd/scripts
for s in $(seq $S0 $((S0+NT-1))); do
  T=$D/${B}_${SOLV}_s${s}_f${NFIX}_p${NPL}_r${RLX}_fl${FL}
  $PY $SC/mkinst2.py $KLEIN/gd_runs/inst/$B.txt $T.txt $s $NFIX $NPL $RLX $FL
  $SC/brute $T.txt > $T.brute
  $KLEIN/gd_runs/$SOLV $T.txt.pin.txt 14 search 1 -1 1 0 0 1 > $T.nosplit 2>/dev/null
  for cfg in "2 3" "3 4" "5 16"; do set -- $cfg
    for p in $(seq 0 $(($2-1))); do $KLEIN/gd_runs/$SOLV $T.txt.pin.txt 14 search 1 $1 $2 $p 0 1 > $T.split$1_$2_$p 2>/dev/null; done
  done
  $PY $SC/check_pinned.py $T
done
