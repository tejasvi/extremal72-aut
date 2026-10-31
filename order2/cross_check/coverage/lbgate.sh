#!/bin/bash
# LTSB gate checks for one rc11 package (coverage-check): stage, ltsbcheck, pinned + whole-orbit + mutant planted tests, verdict
# file, prefix reference (my lwe10b build) and its rc11 identity.  usage: lbgate.sh PKG   (package in struct runs/)
# Base package and code index come from BUILD.txt's first line ("PACKAGE <base> (code index <ci>)"); the base's
# inst.txt.pkl supplies the Gram forms (valid because only the key constraint is rewritten; pin's chain check confirms).
set -u
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
C=<HOME>/c72/audit/c2audit/c3; D=<HOME>/c72/c2opt/struct/runs
PY="nice -n 10 <HOME>/c72/venv/bin/python -I"
p=${1:?package}; P=$D/$p
[ -d $P ] || { echo "no package $P"; exit 1; }
read -r _ base _ _ ci _ < <(head -1 $P/BUILD.txt | tr '()' '  '); ci=${ci%)}
echo "$p: base $base, code index $ci"
[ -f $D/$base/inst.txt.pkl ] || { echo "no base pkl $D/$base/inst.txt.pkl"; exit 1; }
grep -q '^LTSBFILE sym.ltsb' $P/PLAN.txt || { echo "PLAN.txt has no 'LTSBFILE sym.ltsb'"; exit 1; }
( cd $P && sha256sum -c --quiet <(grep -v ' frozen/' INPUTS.sha256) ) && echo "INPUTS OK" || { echo "INPUTS MISMATCH"; exit 1; }
echo "instance lines differing from base: $(diff $P/inst.txt $D/$base/inst.txt | grep -c '^<'), meta: $(diff $P/inst.txt.meta $D/$base/inst.txt.meta | grep -c '^<')"
L=$C/plant/lbprod/$p; mkdir -p $L
for f in inst.txt inst.txt.meta sym.ltsh sym.ltsb key.txt flag.txt PLAN.txt; do ln -sfn $P/$f $L/$f; done
ln -sfn $D/$base/inst.txt.pkl $L/inst.txt.pkl
cd $C
timeout 280 $PY ltsbcheck.py $ci $P/inst.txt $P/sym.ltsh $P/sym.ltsb $P/key.txt > ltsbcheck_$p.txt 2>&1; tail -1 ltsbcheck_$p.txt
cd $C/plant
LTSB=$L/sym.ltsb ENGS="${GATE_ENGS:-lwe10b_lb rc13_lb lwe11b7_lb rc13chk_lb rc11_lb lwe11b5_lb}" timeout 500 ./run_pins.sh $L lbp_$p 4 > runs_lbp_$p.log 2>&1; echo "pinned rc $?"
LTSB=$L/sym.ltsb ENGS="${GATE_ENGS:-lwe10b_lb rc13_lb lwe11b7_lb rc13chk_lb rc11_lb lwe11b5_lb}" ETO=120 timeout 500 ./run_compl.sh $L lbp_$p 3 > compl_lbp_$p.log 2>&1; echo "whole-orbit rc $?"
LTSB=$L/sym.ltsb ENGS="lwe10b_lb mut1_lb mut4_lb" timeout 400 ./run_pins.sh $L lbm_$p 4 > runs_lbm_$p.log 2>&1; echo "mutants rc $?"
cd $C
timeout 60 $PY ltsbplant.py $p
SPL=$(awk '$1=="SPLIT_LEVEL"{print $2}' $P/PLAN.txt)
env -i PATH=/usr/bin:/bin TMPDIR=$TMPDIR LTSHFILE=$P/sym.ltsh LTSBFILE=$P/sym.ltsb timeout 280 nice -n 10 ./lwe10b_ref $P/inst.txt $SPL 2147483647 0 > prefix_$p.txt 2>&1
env -i PATH=/usr/bin:/bin TMPDIR=$TMPDIR LTSHFILE=$P/sym.ltsh LTSBFILE=$P/sym.ltsb timeout 280 nice -n 10 <HOME>/c72/c2opt/alg/frozen_rc13/lwe11 $P/inst.txt $SPL 2147483647 0 > prefix_${p}_rc13.txt 2>&1
a=$(grep -E '^(LEVEL|LBPRUNE|SOLUTION)' prefix_$p.txt | sha256sum | cut -c1-12); b=$(grep -E '^(LEVEL|LBPRUNE|SOLUTION)' prefix_${p}_rc13.txt | sha256sum | cut -c1-12)
echo "prefix lwe10b_ref $a rc13 $b $([ "$a" = "$b" ] && echo IDENTICAL || echo DIFFERENT)"
