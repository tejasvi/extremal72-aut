#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# usage: run_planted.sh INST_BASENAME SOLVER SEED0 NTESTS NFIX NPLANT RELAX FLIPS
# for each test: make sub-instance, brute force, solver without split and with split (depth 2, 3 parts; depth 4, 5 parts)
B=$1; SOLV=$2; S0=$3; NT=$4; NFIX=$5; NPL=$6; RLX=$7; FL=$8
D=$KLEIN/checks/gd/planted; mkdir -p $D
PY=python3
SC=$KLEIN/checks/gd/scripts
for s in $(seq $S0 $((S0+NT-1))); do
  T=$D/${B}_${SOLV}_s${s}_f${NFIX}_p${NPL}_r${RLX}_fl${FL}
  $PY $SC/mkinst.py $KLEIN/gd_runs/inst/$B.txt $T.txt $s $NFIX $NPL $RLX $FL
  $SC/brute $T.txt > $T.brute
  $KLEIN/gd_runs/$SOLV $T.txt 14 search 1 -1 1 0 0 1 > $T.nosplit 2>/dev/null
  for cfg in "2 3" "4 5"; do set -- $cfg
    for p in $(seq 0 $(($2-1))); do $KLEIN/gd_runs/$SOLV $T.txt 14 search 1 $1 $2 $p 0 1 > $T.split$1_$2_$p 2>/dev/null; done
  done
  nb=$(grep -c ^SOLUTION $T.brute); 
  a=$(grep ^SOLUTION $T.brute | sort | md5sum | cut -c1-8)
  b=$(grep ^SOLUTION $T.nosplit | sort | md5sum | cut -c1-8)
  c=$(cat $T.split2_3_* | grep ^SOLUTION | sort | md5sum | cut -c1-8)
  cu=$(cat $T.split2_3_* | grep ^SOLUTION | sort | uniq -d | wc -l)
  d=$(cat $T.split4_5_* | grep ^SOLUTION | sort | md5sum | cut -c1-8)
  du=$(cat $T.split4_5_* | grep ^SOLUTION | sort | uniq -d | wc -l)
  pl=$(sed 's/^/SOLUTION w=/' $T.txt.planted | sort > $T.pl; comm -23 $T.pl <(grep ^SOLUTION $T.brute | sort) | wc -l)
  leaf=$(cat $T.nosplit $T.split* | grep -c LEAF)
  nodes=$(grep -o "nodes [0-9]*" $T.nosplit)
  st="OK"; [ "$a" == "$b" ] && [ "$a" == "$c" ] && [ "$a" == "$d" ] && [ "$pl" == "0" ] || st="FAIL"
  echo "$st $(basename $T) brute_nsol=$nb planted_missing_in_brute=$pl nosplit=$b split23=$c(dup $cu) split45=$d(dup $du) brute=$a leaf=$leaf $nodes"
done
