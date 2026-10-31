#!/bin/bash
# lbtest.sh CI PKGDIR KEYWORDS(comma) TSTAR TAG : probes (PROBES=20000) of the bit-granular LTS prototype src/lwe10b.
# Prints: plain LTSH probe with the instance basis (ub), ub + LTSB, greedy basis plain, greedy basis + LTSB.
# The greedy basis of the first key word comes from src/partsim2.py at level TSTAR; src/rebasis.py rewrites that one
# constraint (raw counts unchanged), src/mkkey.py rebuilds the LTSH with the same key words, src/mkltsb.py the LTSB.
set -u
ci=$1; pk=$2; key=$3; ts=$4; tag=$5; S=<HOME>/c72/c2opt/struct; export TMPDIR=$S/tmp
PY="nice -n 10 <HOME>/c72/venv/bin/python -I"; W=$S/tmp/lb/$tag; mkdir -p $W
k0=${key%%,*}
p() { PROBES=20000 "$@" nice -n 10 $S/src/lwe10b $INST | tail -n 1 | awk '{print $NF}'; }
$PY $S/src/mkkey.py $ci $pk/inst.txt $pk/flag.txt $W/ub.ltsh words:$key > $W/mkkey_ub.log 2>&1
$PY $S/src/mkltsb.py $ci $pk/inst.txt $W/ub.ltsh $W/ub.ltsb > /dev/null
INST=$pk/inst.txt; a=$(p env LTSHFILE=$W/ub.ltsh); b=$(p env LTSHFILE=$W/ub.ltsh LTSBFILE=$W/ub.ltsb)
GB=$(OPENBLAS_NUM_THREADS=1 $PY $S/src/partsim2.py $ci $pk $k0 $ts 200 $ts | grep GREEDY_BASIS | awk '{print $2}')
$PY $S/src/rebasis.py $pk/inst.txt $W/g.txt $k0 $GB > /dev/null
$PY $S/src/mkkey.py $ci $W/g.txt $pk/flag.txt $W/g.ltsh words:$key > $W/mkkey_g.log 2>&1
$PY $S/src/mkltsb.py $ci $W/g.txt $W/g.ltsh $W/g.ltsb > /dev/null
INST=$W/g.txt; c=$(p env LTSHFILE=$W/g.ltsh); d=$(p env LTSHFILE=$W/g.ltsh LTSBFILE=$W/g.ltsb)
echo "$tag ub $a ub+bits $b greedy $c greedy+bits $d  GB=$GB"
