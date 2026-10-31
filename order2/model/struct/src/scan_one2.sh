#!/bin/bash
# scan_one2.sh CI TAG FLAGFILE PROBES : build instance (transient), raw probe profile, checkability key estimates,
# then delete the instance (rebuild with mkinst_c when needed; deterministic).
ci=$1; tag=$2; flag=$3; np=${4:-50000}
D=<HOME>/c72/c2opt/struct
export TMPDIR=$D/tmp
inst=$D/tmp/scan_y${ci}_${tag}.txt
out=$D/logs/scan2/y${ci}_${tag}
[ -s ${out}_key.txt ] && exit 0
grep '^FLAG' $flag > $inst.flag
$D/src/mkinst_c $D/inst/gen$ci.txt $inst.flag $inst > /dev/null || { echo "build fail $ci $tag"; rm -f $inst.flag; exit 1; }
PROBES=$np nice -n 10 $D/src/lwe10 $inst > ${out}_raw.log 2>&1
nice -n 10 <HOME>/c72/venv/bin/python -I $D/src/keycheck.py $ci $inst ${out}_raw.log > ${out}_key.txt 2>&1
nice -n 10 <HOME>/c72/venv/bin/python -I $D/src/keycheck2.py $ci $inst ${out}_raw.log 8 >> ${out}_key.txt 2>&1
echo "FLAGFILE $flag" >> ${out}_key.txt
rm -f $inst $inst.meta $inst.flag
echo "done $ci $tag"
