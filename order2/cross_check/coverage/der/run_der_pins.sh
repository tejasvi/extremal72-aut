#!/bin/bash
# End-to-end planted test of sat's derived ("coset-death") constraints on a real package (audit).
# For each pinned instance P (my pin tool, on the BASE instance: X pinned below level L, real bad sets above):
#   P -> derive.py P P_der --meta [DERIVE_OPTS] -> mkltsh.py (frozen symprep3) -> engines with LTSHFILE = P_der.ltsh
#   and, as a baseline, the engines on P itself with the package's sym.ltsh.  pin verify (on the base instance) must
#   report the K-minimal X kept (min) or pruned (nonmin), and the derived run must report exactly the baseline's
#   solutions (derived constraints are implied, so they never remove a solution).
# usage: run_der_pins.sh PKGDIR CI TAG NSEED      (env DERIVE_OPTS, ENGS; prep.txt from plant/runs/<pkg>/)
set -u
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
C=<HOME>/c72/audit/c2audit/c3; H=$C/plant; S=<HOME>/c72/c2opt/sat/src
PY="nice -n 10 <HOME>/c72/venv/bin/python -I"
P=$1; CI=$2; TAG=$3; NS=${4:-2}; DOPT=${DERIVE_OPTS:---maxlev 7}
SPL=$(awk '/^SPLIT_LEVEL/{print $2}' $P/PLAN.txt); L=${PINL:-$((SPL+2))}
declare -A ENG=( [lwe8ref]=$C/lwe8_ref [rc9]=<HOME>/c72/c2opt/alg/frozen_rc9/lwe11 [rc11]=<HOME>/c72/c2opt/alg/frozen_rc11/lwe11 )
ORDER=${ENGS:-lwe8ref rc9}
PREP=$H/runs/$(basename $P)/prep.txt; [ -s $PREP ] || { echo "no prep.txt for $(basename $P)"; exit 1; }
read -a ODD < $PREP.odd
W=$C/der/runs/$TAG; mkdir -p $W; cd $W
for s in $(seq 1 $NS); do
  for mode in 0 1; do
    h=0; if [ $mode = 1 ]; then [ ${#ODD[@]} -gt 0 ] || continue; h=${ODD[$(( (s*7919) % ${#ODD[@]} ))]}; fi
    for w in min nonmin; do
      b=pin_s${s}_m${mode}_$w
      info=$(timeout 300 nice -n 10 $H/pin make $PREP $P/inst.txt $P/key.txt $b.txt $s $mode $h $L $w 2>&1 | tail -1)
      [ -s $b.txt ] || { echo "$TAG s$s m$mode $w MAKE: $info"; continue; }
      cp $P/inst.txt.meta $b.txt.meta
      dinfo=$(timeout 280 $PY ${DERIVE_PY:-$S/derive.py} $b.txt ${b}_der.txt --meta $DOPT 2>&1 | tail -1)
      timeout 280 $PY $S/mkltsh.py $CI ${b}_der.txt $P/flag.txt $P/key.txt ${b}_der.ltsh > /dev/null 2>&1 || { echo "$TAG $b MKLTSH FAILED"; continue; }
      for e in $ORDER; do
        for v in base der; do
          if [ $v = base ]; then inst=$b.txt; lt=$P/sym.ltsh; else inst=${b}_der.txt; lt=${b}_der.ltsh; fi
          out=out_${b}_${e}_$v.txt
          env -i PATH=/usr/bin:/bin TMPDIR=$TMPDIR LTSHFILE=$lt timeout 240 nice -n 10 ${ENG[$e]} $inst > $out 2>&1
        done
        vb=$(timeout 300 nice -n 10 $H/pin verify $PREP $P/inst.txt $P/key.txt $s $mode $h $w < out_${b}_${e}_base.txt 2>&1 | tail -1)
        vd=$(timeout 300 nice -n 10 $H/pin verify $PREP $P/inst.txt $P/key.txt $s $mode $h $w < out_${b}_${e}_der.txt 2>&1 | tail -1)
        sb=$(grep '^SOLUTION' out_${b}_${e}_base.txt | sort | sha256sum | cut -c1-12); sd=$(grep '^SOLUTION' out_${b}_${e}_der.txt | sort | sha256sum | cut -c1-12)
        nb=$(awk '/^LEVEL/{n+=$8} END{print n+0}' out_${b}_${e}_base.txt); nd=$(awk '/^LEVEL/{n+=$8} END{print n+0}' out_${b}_${e}_der.txt)
        st=$(cat out_${b}_${e}_base.txt out_${b}_${e}_der.txt | grep -c STOPPED)
        echo "$TAG s$s m$mode $w $e stopped=$st solutions $([ "$sb" = "$sd" ] && echo same || echo DIFFERENT) nodes base $nb der $nd | der: $vd | base: $vb"
      done
      echo "   [$info] [$dinfo]"
      rm -f $b.txt ${b}_der.txt
    done
  done
done
