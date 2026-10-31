#!/bin/bash
# <CPU> LTSB task (audit code).  partb: with LTSBFILE, reference lwe10b (7766661c) + lwe10b_b5 (246ceb0b, the build that
# the AVX2 fleet boxes use as cross-check reference) + lwe11b5 [+ lwe11b5 under LWE11CHECK]; part: without LTSB,
# reference lwe8 + lwe11b5.  The final step is exec'd: a task is one python process plus at most one engine process.
KIT=$(cd "$(dirname "$0")" && pwd); export TMPDIR=$KIT/tmp; mkdir -p $TMPDIR $KIT/logs $KIT/work
ulimit -v 2000000
unset LTSHFILE LTSBFILE SYMFILE LTSFILE PROBES ALARM LWE11CHECK
PY=$HOME/venv/bin/python; [ -x $PY ] || PY=python3
set -- $*
mode=$1; pkg=$2; spl=$3; np=$4; parts=$5; tag=$6; chk=${7:-0}; P=$KIT/pkgs/$pkg; S=$KIT/scripts; B=$KIT/bin
f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
case $mode in
  partb) ENG="--eng lwe10b=$B/lwe10b --eng lwe10b_b5=$B/lwe10b_b5 --eng lwe11b5=$B/lwe11b5"; [ "$chk" = 1 ] && ENG="$ENG --eng lwe11b5chk=$B/lwe11b5chk"
         exec nice -n 10 $PY -I $S/difftest_c2.py part $P $spl $np $parts --ltsb $ENG --tag $tag --work $KIT/work/$tag --tmo 14400 > $f 2>&1 ;;
  part)  ENG="--eng lwe8=$B/lwe8 --eng lwe11b5=$B/lwe11b5"
         exec nice -n 10 $PY -I $S/difftest_c2.py part $P $spl $np $parts $ENG --tag $tag --work $KIT/work/$tag --tmo 14400 > $f 2>&1 ;;
esac
