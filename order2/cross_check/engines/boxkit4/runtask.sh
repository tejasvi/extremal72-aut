#!/bin/bash
# One differential-test task (line of tasks*.txt).  KIT = directory of this script.  Audit code.
# The final step is exec'd, so a running task is one python process plus at most one engine process.
KIT=$(cd "$(dirname "$0")" && pwd); export TMPDIR=$KIT/tmp; mkdir -p $TMPDIR $KIT/logs $KIT/work
ulimit -v 1000000
unset LTSHFILE SYMFILE LTSFILE PROBES ALARM
PY=$HOME/venv/bin/python; [ -x $PY ] || PY=python3
set -- $*
mode=$1; pkg=$2; P=$KIT/pkgs/$pkg; S=$KIT/scripts; B=$KIT/bin
ENG="--eng lwe8=$B/lwe8 --eng rc9=$B/rc9 --eng lwe11b3=$B/lwe11b3"
[ -n "$ENGSET" ] && ENG=$(echo "$ENGSET" | sed "s#BIN#$B#g")
[ -n "$EXTRA_ENG" ] && ENG="$ENG $EXTRA_ENG"
case $mode in
  part) tag=$6; f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
        exec nice -n 10 $PY -I $S/difftest_c2.py part $P $3 $4 $5 $ENG --tag $tag --work $KIT/work/$tag --tmo 7200 > $f 2>&1 ;;
  pin|pinns) L=$3; npref=$4; seed=$5; var=$6; spl2=$7; np2=$8; tag=$9; f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
        PROBES=400000 PFXLEV=$L PSEED=$seed LTSHFILE=$P/sym.ltsh nice -n 10 $B/lwe8_pfx $P/inst.txt | grep PREFIX > $KIT/work/$tag.pfx
        NS=""; [ $mode = pinns ] && NS="--nosym"
        exec nice -n 10 $PY -I $S/difftest_c2.py pin $P $L $KIT/work/$tag.pfx $npref $seed $var $spl2 $np2 $NS $ENG --tag $tag --work $KIT/work/$tag --tmo 3600 > $f 2>&1 ;;
  core) L=$3; npref=$4; seed=$5; q=$6; tag=$7; f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
        cd $KIT/work; export ADDBAD=2 DIFF_TIMEOUT=1800
        exec nice -n 10 $PY -I $S/core_test.py $P/inst.txt $L $npref $seed $q $B/lwe8 $tag > $f 2>&1 ;;
esac
