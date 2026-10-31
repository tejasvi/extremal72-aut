#!/bin/bash
# fixmid.sh CI TAG BASEFLAG K WORD : (box) flag = first K vectors of BASEFLAG + the G-fixed word WORD, continued by
# flagbeam4 (MAXL beam 1000/3000, total-nodes beam 1000/3000); for each variant build the instance, an early:8 key
# (k0 = earliest complete orbit, i.e. the fixed word if it is earliest) and run raw + LTS probes (PROBES=20000).
# Output: one line per variant in <HOME>/struct/fixmid/CI_TAG_V.txt
ci=$1; tag=$2; bf=$3; k=$4; w=$5; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/fixmid $B/var
pre=$(grep '^FLAG' $bf | awk -v k=$k '{s=""; for (i=2; i<=k+1; i++) s=s $i ","; print s}')${w}
for v in m1000 m3000 l1000 l3000; do
  ( n=${ci}_${tag}_$v; f=$B/var/fm$n.flag; o=$B/fixmid/$n.txt; [ -s $o ] && exit 0
    b=${v:1}; if [ ${v:0:1} = m ]; then E="MAXL=1"; else E=""; fi
    [ -s $f ] || env $E nice -n 10 $B/src/flagbeam4 $B/inst/data/gen_$ci.txt $B/inst/data/low_$ci.txt $b "$pre" 2> /dev/null | grep "^FLAG" > $f
    [ -s $f ] || { echo "$n noflag" > $o; exit 0; }
    d=$TMPDIR/fm_$n; mkdir -p $d; grep '^FLAG' $f > $d/flag.txt
    $B/src/mkinst_c $B/inst/gen$ci.txt $d/flag.txt $d/inst.txt > /dev/null || { echo "$n buildfail" > $o; exit 0; }
    <HOME>/venv/bin/python -I $B/src/mkkey.py $ci $d/inst.txt $d/flag.txt $d/sym.ltsh early:8 > $d/mkkey.log 2>&1
    r=$(PROBES=20000 nice -n 10 $B/runs/frozen3/lwe10 $d/inst.txt | tail -n 1 | awk '{print $NF}')
    l=$(PROBES=20000 LTSHFILE=$d/sym.ltsh nice -n 10 $B/runs/frozen3/lwe10 $d/inst.txt | tail -n 1 | awk '{print $NF}')
    echo "$n raw $r lts $l $(grep -h 'key levels' $d/mkkey.log | tail -n 1) $(grep -h '^KEY' $d/mkkey.log | tail -n 1 | cut -c1-60)" > $o
    rm -f $d/inst.txt $d/inst.txt.meta ) &
done; wait
