#!/bin/bash
# bbtest.sh NAME CI FLAGFILE KEY TSTAR : (box) mkinst_c ("box build") instance of FLAGFILE + KEY, then greedy rebasis + LTSH +
# LTSB as in src/mklb.sh; probes (PROBES=20000): plain LTS, greedy, greedy+LTSB.  Directory <HOME>/struct/bb/NAME.
n=$1; ci=$2; ff=$3; key=$4; ts=$5; B=<HOME>/struct; W=$B/bb/$n; mkdir -p $W; export TMPDIR=$B/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
PY="nice -n 10 $HOME/venv/bin/python -I"; k0=${key%%,*}
grep '^FLAG' $ff > $W/flag.txt; $B/src/mkinst_c $B/inst/gen$ci.txt $W/flag.txt $W/inst.txt > /dev/null
$PY $B/src/mkkey.py $ci $W/inst.txt $W/flag.txt $W/sym_plain.ltsh words:$key > $W/mk_plain.log 2>&1
GB=$($PY $B/src/partsim2.py $ci $W $k0 $ts 200 $ts | grep GREEDY_BASIS | awk '{print $2}')
mkdir -p $W/lb; $PY $B/src/rebasis.py $W/inst.txt $W/lb/inst.txt $k0 $GB > /dev/null
$PY $B/src/mkkey.py $ci $W/lb/inst.txt $W/flag.txt $W/lb/sym.ltsh words:$key > $W/lb/mk.log 2>&1
$PY $B/src/mkltsb.py $ci $W/lb/inst.txt $W/lb/sym.ltsh $W/lb/sym.ltsb > /dev/null
p=$(PROBES=20000 LTSHFILE=$W/sym_plain.ltsh nice -n 10 $B/runs/frozen3/lwe10 $W/inst.txt | tail -n 1 | awk '{print $NF}')
a=$(PROBES=20000 LTSHFILE=$W/lb/sym.ltsh nice -n 10 $B/src/lwe10b $W/lb/inst.txt | tail -n 1 | awk '{print $NF}')
b=$(PROBES=20000 LTSHFILE=$W/lb/sym.ltsh LTSBFILE=$W/lb/sym.ltsb nice -n 10 $B/src/lwe10b $W/lb/inst.txt | tail -n 1 | awk '{print $NF}')
echo "$n boxbuild plain $p greedy $a greedy+LTSB $b GB $GB"
