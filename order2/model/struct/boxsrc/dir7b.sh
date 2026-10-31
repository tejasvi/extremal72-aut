#!/bin/bash
# dir7b.sh CODE CI V1DIR NPROC : (box) STRUCT direction 7, version 2: per-subtree continuation chosen by REAL subtree probes.
# For each level-3 node of V1DIR/nodes.txt (from dir7.sh): candidates = the package flag and flagbeam4 continuations of its
# first 3 vectors (conditional weights of that node, src/condw.py: beams 300/1000/3000, objectives total/MAXL; global weights:
# beams 300/3000, MAXL).  Each candidate is scored by 2000 random dives from the node (raw; lwe10n_p STARTASG+PROBES); the
# best candidate's exact raw subtree is then counted.  Output r<id>.txt: id default_raw best_tag best_probe best_exact default_probe
code=$1; ci=$2; V=$3; P=$4; B=<HOME>/struct; R=$B/runs/$code; W=${V}_b; mkdir -p $W
export TMPDIR=$B/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
pre=$(grep '^FLAG' $R/flag.txt | awk '{print $2","$3","$4}')
cat $V/nodes.txt | xargs -P $P -L 1 bash -c '
  id=$1; a=$2; ci='"$ci"'; B='"$B"'; R='"$R"'; V='"$V"'; W='"$W"'; pre='"$pre"'
  o=$W/r$id.txt; [ -s $o ] && exit 0
  pr() { STARTASG=$a STARTLEVEL=3 PROBES=2000 nice -n 10 $B/src/lwe10n_p $1 | tail -n 1 | awk "{print \$NF}"; }
  ex() { STARTASG=$a STARTLEVEL=3 nice -n 10 $B/src/lwe10n_p $1 | awk "/^LEVEL/ {s += \$8} END {print s}"; }
  dr=$(awk "\$1 == \"$id\" {print \$5}" $V/r$id.txt 2>/dev/null); [ -n "$dr" ] || dr=$(ex $R/inst.txt)
  <HOME>/venv/bin/python -I $B/src/condw.py $R/inst.txt $a 3 $W/n$id.low > /dev/null
  dp=$(pr $R/inst.txt); best=default; bp=$dp
  for c in n300l n1000l n3000l n300m n1000m n3000m g300m g3000m; do
    bm=${c:1}; bm=${bm%?}; ob=${c: -1}; if [ ${c:0:1} = n ]; then lf=$W/n$id.low; else lf=$B/inst/data/low_$ci.txt; fi
    if [ $ob = m ]; then E="MAXL=1"; else E="X=1"; fi
    env $E nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $lf $bm $pre 2> /dev/null | grep "^FLAG" > $W/n${id}_$c.flag
    $B/src/mkinst_c $B/inst/gen$ci.txt $W/n${id}_$c.flag $W/n${id}_$c.inst > /dev/null
    p=$(pr $W/n${id}_$c.inst)
    if awk -v x=$p -v y=$bp "BEGIN {exit !(x < y)}"; then best=$c; bp=$p; fi
    [ $c = $best ] || rm -f $W/n${id}_$c.inst $W/n${id}_$c.inst.meta
  done
  if [ $best = default ]; then be=$dr; else be=$(ex $W/n${id}_$best.inst); fi
  rm -f $W/n${id}_*.inst $W/n${id}_*.inst.meta $W/n$id.low
  echo "$id default_raw $dr best $best best_probe $bp best_exact $be default_probe $dp" > $o'
cat $W/r*.txt > $W/results.txt; echo "done $(wc -l < $W/results.txt)"
