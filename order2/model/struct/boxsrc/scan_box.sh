#!/bin/bash
# scan_box.sh CI TAG FLAGFILE [PROBES] : (box) transient instance, raw probe, checkability-key model; resumable
ci=$1; tag=$2; flag=$3; np=${4:-50000}; B=<HOME>/struct; export TMPDIR=$B/tmp
out=$B/scan/y${ci}_${tag}; mkdir -p $B/scan
[ -s ${out}_key.txt ] && grep -q FLAGFILE ${out}_key.txt && exit 0
inst=$TMPDIR/sc_y${ci}_${tag}.txt
grep '^FLAG' $flag > $inst.flag
$B/src/mkinst_c $B/inst/gen$ci.txt $inst.flag $inst > /dev/null || { echo "build fail $ci $tag"; rm -f $inst.flag; exit 1; }
PROBES=$np nice -n 10 $B/src/lwe10 $inst > ${out}_raw.log 2>&1
nice -n 10 <HOME>/venv/bin/python -I $B/src/keycheck.py $ci $inst ${out}_raw.log > ${out}_key.tmp 2>&1
nice -n 10 <HOME>/venv/bin/python -I $B/src/keycheck2.py $ci $inst ${out}_raw.log 8 >> ${out}_key.tmp 2>&1
echo "FLAGFILE $flag" >> ${out}_key.tmp; mv ${out}_key.tmp ${out}_key.txt
rm -f $inst $inst.meta $inst.flag
