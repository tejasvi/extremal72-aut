#!/bin/bash
# mkfs2cand.sh CI FLAGFILE NAME : (box) candidate dir runs/NAME from a flagsearch2 winner: instance (mkinst_c), the key
# type recorded in the .res file next to the flag (early:8 or h0fix:BESTWORDS of keycheck.py), LTS probe + level profile
ci=$1; ff=$2; n=$3; B=<HOME>/struct; export TMPDIR=$B/tmp; d=$B/runs/$n; mkdir -p $d
grep '^FLAG' $ff > $d/flag.txt
$B/src/mkinst_c $B/inst/gen$ci.txt $d/flag.txt $d/inst.txt > /dev/null
kt=$(awk '{print $2}' ${ff%.flag}.res)
if [ "$kt" = early ]; then spec=early:8; else
  PROBES=20000 nice -n 10 $B/runs/frozen3/lwe10 $d/inst.txt > $d/raw.log
  bw=$(<HOME>/venv/bin/python -I $B/src/keycheck.py $ci $d/inst.txt $d/raw.log | grep BESTWORDS | awk '{print $2}' | cut -d, -f1-8); spec=h0fix:$bw; fi
<HOME>/venv/bin/python -I $B/src/mkkey.py $ci $d/inst.txt $d/flag.txt $d/sym.ltsh $spec > $d/mkkey.log 2>&1
echo "$n key $kt $(grep -o 'key levels.*' $d/mkkey.log) $(PROBES=20000 LTSHFILE=$d/sym.ltsh nice -n 10 $B/runs/frozen3/lwe10 $d/inst.txt | tr '\n' ' ' | cut -c1-260)"
