#!/bin/bash
# scan_one.sh CI FLAGTAG FLAGFILE PROBES : build instance, raw probe profile, checkability key estimates
ci=$1; tag=$2; flag=$3; np=${4:-50000}
D=<HOME>/c72/c2opt/struct
export TMPDIR=$D/tmp
inst=$D/inst/scan/y${ci}_${tag}.txt
[ -s $inst ] || $D/src/mkinst_c $D/inst/gen$ci.txt $flag $inst > /dev/null
PROBES=$np nice -n 10 $D/src/lwe10 $inst > $D/logs/scan/y${ci}_${tag}_raw.log 2>&1
nice -n 10 <HOME>/c72/venv/bin/python -I $D/src/keycheck.py $ci $inst $D/logs/scan/y${ci}_${tag}_raw.log > $D/logs/scan/y${ci}_${tag}_key.txt 2>&1
echo "done $ci $tag"
