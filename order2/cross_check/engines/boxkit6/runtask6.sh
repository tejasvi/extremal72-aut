#!/bin/bash
# rc13/lwe11b7 wave task (audit code, 2026-10-22).  The final step is exec'd: a task is at most two processes.
#   partb PKG SPL NPART PARTS TAG CHK   with LTSBFILE: reference lwe10b, then rc11, rc13, lwe11b7 (CHK r: + rc13 under
#                                       LWE11CHECK, b: + lwe11b7 under LWE11CHECK)
#   part  PKG SPL NPART PARTS TAG       without LTSB: reference lwe8, then rc13, lwe11b7
#   pinb  PKG L NPREF SEED VARIANTS SPL2 NPART2 TAG CHK   pinned sub-instances with their own LTSB file (pinltsb.py)
#   pin   PKG L NPREF SEED VARIANTS SPL2 NPART2 TAG       pinned sub-instances without LTSB
KIT=$(cd "$(dirname "$0")" && pwd); export TMPDIR=$KIT/tmp; mkdir -p $TMPDIR $KIT/logs $KIT/work
ulimit -v 2000000
unset LTSHFILE LTSBFILE SYMFILE LTSFILE PROBES ALARM LWE11CHECK LWE11NOFUSE LWE11THR LWE11NOSKIP LWE11NOBULK LWE11NOTIESKIP LWE11OFF LWE11NOFASTSPLIT
PY=$HOME/venv/bin/python; [ -x $PY ] || PY=python3
set -- $*
mode=$1; pkg=$2; P=$KIT/pkgs/$pkg; S=$KIT/scripts; B=$KIT/bin
EB="--eng lwe10b=$B/lwe10b --eng rc11=$B/rc11 --eng rc13=$B/rc13 --eng lwe11b7=$B/lwe11b7"
EP="--eng lwe8=$B/lwe8 --eng rc13=$B/rc13 --eng lwe11b7=$B/lwe11b7"
chkeng() { case "$1" in *r*) echo -n " --eng rc13chk=$B/rc13chk";; esac; case "$1" in *b*) echo -n " --eng lwe11b7chk=$B/lwe11b7chk";; esac; }
case $mode in
  partb|part) tag=$6; f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
        if [ $mode = partb ]; then ENG="$EB$(chkeng ${7:-0})"; LB=--ltsb; else ENG="$EP"; LB=""; fi
        exec nice -n 10 $PY -I $S/difftest_c2.py part $P $3 $4 $5 $LB $ENG --tag $tag --work $KIT/work/$tag --tmo 7200 > $f 2>&1 ;;
  pinb|pin) L=$3; npref=$4; seed=$5; var=$6; spl2=$7; np2=$8; tag=$9; f=$KIT/logs/$tag.log; grep -q '^SUMMARY' $f 2>/dev/null && exit 0
        PROBES=20000 PFXLEV=$L PSEED=$seed LTSHFILE=$P/sym.ltsh nice -n 10 $B/lwe8_pfx $P/inst.txt > $KIT/work/$tag.pfxraw
        grep PREFIX $KIT/work/$tag.pfxraw > $KIT/work/$tag.pfx; rm -f $KIT/work/$tag.pfxraw
        if [ $mode = pinb ]; then ENG="$EB$(chkeng ${10:-0})"; LB=--ltsb; else ENG="$EP"; LB=""; fi
        exec nice -n 10 $PY -I $S/difftest_c2.py pin $P $L $KIT/work/$tag.pfx $npref $seed $var $spl2 $np2 $LB $ENG --tag $tag --work $KIT/work/$tag --tmo 1800 > $f 2>&1 ;;
esac
