#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# planted solutions in the FULL instance (no variables fixed), production solver configuration.
# usage: run_planted_full.sh INST SOLVER SEED NPLANT FLIPS
B=$1; SOLV=$2; s=$3; NPL=$4; FL=$5
D=$KLEIN/checks/gd/plantedfull; mkdir -p $D
PY=python3; SC=$KLEIN/checks/gd/scripts
T=$D/${B}_${SOLV}_s${s}_p${NPL}_fl${FL}
$PY $SC/mkinst.py $KLEIN/gd_runs/inst/$B.txt $T.txt $s 0 $NPL 0 $FL
$KLEIN/gd_runs/$SOLV $T.txt 14 search 1 -1 1 0 0 1 > $T.nosplit 2>/dev/null
for p in $(seq 0 15); do $KLEIN/gd_runs/$SOLV $T.txt 14 search 1 5 16 $p 0 1 > $T.part$p 2>/dev/null; done
$PY $SC/check_full.py $T
