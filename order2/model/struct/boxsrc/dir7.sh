#!/bin/bash
# dir7.sh CODE CI NPART BEAM OBJ NPROC KEY : (box) STRUCT direction 7, per-subtree re-optimised flags, measured.
# Level-3 nodes of package runs/CODE (every NPART-th LTS-surviving node, lwe10n NODEOUT); for each node: subtree size with
# the package flag (LTS with the package key, and raw), and with a flag whose continuation after the first 3 vectors is
# re-optimised by flagbeam4 (beam BEAM, objective OBJ: l = total nodes, m = MAXL) using the node's conditional low-word
# weights (src/condw.py) -- and, as a control, using the global weights (inst/data/low_CI.txt).  Same key words.
code=$1; ci=$2; np=$3; beam=$4; obj=$5; P=$6; key=$7; B=<HOME>/struct; R=$B/runs/$code; W=$B/dir7/${code}_${obj}${beam}; mkdir -p $W
export TMPDIR=$B/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
pre=$(grep '^FLAG' $R/flag.txt | awk '{print $2","$3","$4}')
[ -s $W/nodes.txt ] || NODEOUT=1 LTSHFILE=$R/sym.ltsh nice -n 10 $B/src/lwe10n $R/inst.txt 3 $np 0 | grep '^NODE' > $W/nodes.txt
echo "nodes: $(wc -l < $W/nodes.txt)"
cat $W/nodes.txt | xargs -P $P -L 1 bash -c '
  id=$1; a=$2; code='"$code"'; ci='"$ci"'; beam='"$beam"'; obj='"$obj"'; B='"$B"'; R='"$R"'; W='"$W"'; key='"$key"'; pre='"$pre"'
  o=$W/r$id.txt; [ -s $o ] && exit 0
  sz() { awk "/^LEVEL/ {s += \$8} END {print s}"; }
  dl=$(STARTASG=$a STARTLEVEL=3 LTSHFILE=$R/sym.ltsh nice -n 10 $B/src/lwe10n $R/inst.txt | sz)
  dr=$(STARTASG=$a STARTLEVEL=3 nice -n 10 $B/src/lwe10n $R/inst.txt | sz)
  <HOME>/venv/bin/python -I $B/src/condw.py $R/inst.txt $a 3 $W/n$id.low > $W/n$id.condw
  res="$id default_lts $dl default_raw $dr"
  for v in node glob; do
    if [ $v = node ]; then lf=$W/n$id.low; else lf=$B/inst/data/low_$ci.txt; fi
    if [ $obj = m ]; then E="MAXL=1"; else E="X=1"; fi
    env $E nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $lf $beam $pre 2> /dev/null | grep "^FLAG" > $W/n${id}_$v.flag
    $B/src/mkinst_c $B/inst/gen$ci.txt $W/n${id}_$v.flag $W/n${id}_$v.inst > /dev/null
    <HOME>/venv/bin/python -I $B/src/mkkey.py $ci $W/n${id}_$v.inst $W/n${id}_$v.flag $W/n${id}_$v.ltsh words:$key > /dev/null 2>&1
    same=$(cmp -s <(head -n 2 $R/inst.txt | tail -n 1 | cut -d" " -f1-4) <(head -n 2 $W/n${id}_$v.inst | tail -n 1 | cut -d" " -f1-4) && echo ok || echo DIFF)
    nl=$(STARTASG=$a STARTLEVEL=3 LTSHFILE=$W/n${id}_$v.ltsh nice -n 10 $B/src/lwe10n $W/n${id}_$v.inst | sz)
    nr=$(STARTASG=$a STARTLEVEL=3 nice -n 10 $B/src/lwe10n $W/n${id}_$v.inst | sz)
    res="$res ${v}_lts $nl ${v}_raw $nr vstart03 $same"
    rm -f $W/n${id}_$v.inst $W/n${id}_$v.inst.meta $W/n${id}_$v.inst.pkl $W/n${id}_$v.ltsh
  done
  rm -f $W/n$id.low
  echo "$res" > $o'
cat $W/r*.txt > $W/results.txt; echo "done $(wc -l < $W/results.txt)"
