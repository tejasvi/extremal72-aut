#!/bin/bash
# planted-solution test: planted_test.sh THR NUM SEED MINK GUIDEDEPTH
# GUIDEDEPTH = 0: whole depth-1 subtree searched; 1: row at pos 3 forced; 2: rows at pos 3 and 2 forced.
# The searches for the NUM planted matrices run in parallel (each search is single-threaded in node1 mode).
cd "$(dirname "$0")/.."
THR=$1; NUM=$2; SEED=$3; MINK=$4; GD=$5
tag=t${THR}_s${SEED}_m${MINK}_g${GD}
OMP_NUM_THREADS=${PG_THREADS:-8} nice -n 10 src/planted $THR $NUM $SEED $MINK > logs/planted_$tag.log 2>&1
grep '^CANON' logs/planted_$tag.log | while read -r line; do
  id=$(echo "$line" | awk '{print $2}')
  k0=$(echo "$line" | sed 's/.*K0=\([0-9]*\).*/\1/')
  n1=$(echo "$line" | sed 's/.*node1=\([0-9a-f]*\).*/\1/')
  g=$(echo "$line" | sed 's/.*guide(pos3,pos2)=\([0-9a-f]*\),\([0-9a-f]*\).*/\1 \2/')
  mat=$(echo "$line" | sed 's/.*matrix: //')
  case $GD in 0) G="";; 1) G=$(echo $g | awk '{print $1}');; 2) G="$g";; esac
  out=logs/planted_${tag}_$id.out
  rm -f $out.sol
  (
    GUIDE="$G" SOLFILE=$out.sol OMP_NUM_THREADS=${PT_THREADS:-4} nice -n 10 src/search $THR $k0 node1 $n1 > $out 2>&1
    nsol=$(grep -c '^SOL' $out.sol 2>/dev/null)
    if grep -q "SOL K0=$k0 $mat\$" $out.sol 2>/dev/null; then res=FOUND; else res=MISSING; fi
    echo "planted $id THR=$THR K0=$k0 node1=$n1 guide='$G' solutions_in_subtree=$nsol -> $res"
  ) &
done
wait
