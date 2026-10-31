#!/bin/bash
# rc11 wave task.  partb: with LTSBFILE, reference lwe10b (+ rc11, lwe11b5[, rc11chk]); part: without LTSB, reference lwe8.
KIT=$(cd "$(dirname "$0")" && pwd); export TMPDIR=$KIT/tmp; mkdir -p $TMPDIR $KIT/logs $KIT/work
ulimit -v 2000000
unset LTSHFILE LTSBFILE SYMFILE LTSFILE PROBES ALARM LWE11CHECK
PY=$HOME/venv/bin/python; [ -x $PY ] || PY=python3
set -- $*
mode=$1; pkg=$2; spl=$3; np=$4; parts=$5; tag=$6; chk=${7:-0}; P=$KIT/pkgs/$pkg; S=$KIT/scripts; B=$KIT/bin
f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
case $mode in
  partb) ENG="--eng lwe10b=$B/lwe10b --eng rc11=$B/rc11 --eng lwe11b5=$B/lwe11b5"; [ "$chk" = 1 ] && ENG="$ENG --eng rc11chk=$B/rc11chk"
         exec nice -n 10 $PY -I $S/difftest_c2.py part $P $spl $np $parts --ltsb $ENG --tag $tag --work $KIT/work/$tag --tmo 14400 > $f 2>&1 ;;
  part)  ENG="--eng lwe8=$B/lwe8 --eng rc11=$B/rc11 --eng lwe11b5=$B/lwe11b5"
         exec nice -n 10 $PY -I $S/difftest_c2.py part $P $spl $np $parts $ENG --tag $tag --work $KIT/work/$tag --tmo 14400 > $f 2>&1 ;;
esac
