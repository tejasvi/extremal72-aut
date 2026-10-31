#!/bin/bash
# Pinned single-member LTS tests for one package with several engines (audit).  usage: run_pins.sh PKGDIR TAG NSEED
# Env: ENGS (engine list, default lwe8ref rc7 lwe11b lwe10 c2e_lwe11; also rc9, lwe11b3), PINL (pin level).
set -u
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
H=<HOME>/c72/audit/c2audit/c3/plant; P=$1; TAG=$2; NS=${3:-3}
CI=$(grep -o 'index in codes36.txt: [0-9]*' $P/PLAN.txt | awk '{print $NF}')
SPL=$(awk '/^SPLIT_LEVEL/{print $2}' $P/PLAN.txt); L=${PINL:-$((SPL+2))}
cd $H; mkdir -p runs/$TAG; cd runs/$TAG
nice -n 10 <HOME>/c72/venv/bin/python -I $H/prep_plant.py $P $CI prep.txt > prep.log 2>&1 || { echo "$TAG PREP FAILED"; cat prep.log; exit 1; }
read -a ODD < prep.txt.odd
declare -A ENG=( [lwe8ref]=$H/../lwe8_ref [rc7]=<HOME>/c72/c2opt/alg/frozen_rc7/lwe11 [lwe11b]=<HOME>/c72/fleet/kit/lwe11b/lwe11b [lwe10]=<HOME>/c72/explore/runs2/frozen3/lwe10 [c2e_lwe11]=<HOME>/c72/explore/runs2/frozen4/lwe11 [rc9]=<HOME>/c72/fleet/kit/rc9/lwe11 [lwe11b3]=<HOME>/c72/fleet/kit/lwe11b3/lwe11b [lwe10b]=<HOME>/c72/c2opt/struct/src/lwe10b [lwe10b_lb]=<HOME>/c72/c2opt/struct/src/lwe10b [mut1_lb]=<HOME>/c72/audit/c2audit/c3/plant/mut/lwe10b_mut1 [mut4_lb]=<HOME>/c72/audit/c2audit/c3/plant/mut/lwe10b_mut4 [rc11]=<HOME>/c72/c2opt/alg/frozen_rc11/lwe11 [rc11_lb]=<HOME>/c72/c2opt/alg/frozen_rc11/lwe11 [rc11chk_lb]=<HOME>/c72/c2opt/alg/frozen_rc11/lwe11 [lwe11b5]=<HOME>/c72/c2opt/alg/frozen_b5/lwe11b [lwe11b5_lb]=<HOME>/c72/c2opt/alg/frozen_b5/lwe11b [lwe11b5chk_lb]=<HOME>/c72/c2opt/alg/frozen_b5/lwe11b [rc13]=<HOME>/c72/c2opt/alg/frozen_rc13/lwe11 [rc13_lb]=<HOME>/c72/c2opt/alg/frozen_rc13/lwe11 [rc13chk_lb]=<HOME>/c72/c2opt/alg/frozen_rc13/lwe11 [lwe11b7]=<HOME>/c72/c2opt/alg/frozen_b7/lwe11b [lwe11b7_lb]=<HOME>/c72/c2opt/alg/frozen_b7/lwe11b [rc14]=<HOME>/c72/c2opt/alg/frozen_rc14/lwe11 [rc14_lb]=<HOME>/c72/c2opt/alg/frozen_rc14/lwe11 [rc14chk_lb]=<HOME>/c72/c2opt/alg/frozen_rc14/lwe11 [rc14g40]=<HOME>/c72/c2opt/alg/frozen_rc14g/y40/lwe11 [rc14g40chk]=<HOME>/c72/c2opt/alg/frozen_rc14g/y40/lwe11 [rc14g12_lb]=<HOME>/c72/c2opt/alg/frozen_rc14g/y12-lb2/lwe11 [rc14g12chk_lb]=<HOME>/c72/c2opt/alg/frozen_rc14g/y12-lb2/lwe11 [rc14g15_lb]=<HOME>/c72/c2opt/alg/frozen_rc14g/y15-lb/lwe11 [rc14g15chk_lb]=<HOME>/c72/c2opt/alg/frozen_rc14g/y15-lb/lwe11 )
for s in $(seq 1 $NS); do
  for mode in 0 1; do
    h=0; if [ $mode = 1 ]; then [ ${#ODD[@]} -gt 0 ] || continue; h=${ODD[$(( (s*7919) % ${#ODD[@]} ))]}; fi
    for w in min nonmin; do
      inst=pin_s${s}_m${mode}_$w.txt
      info=$(timeout 300 nice -n 10 $H/pin make prep.txt $P/inst.txt $P/key.txt $inst $s $mode $h $L $w 2>&1 | tail -1)
      [ -s $inst ] || { echo "$TAG s$s m$mode $w MAKE: $info"; continue; }
      ref=""
      for e in ${ENGS:-lwe8ref rc7 lwe11b lwe10 c2e_lwe11}; do
        out=out_s${s}_m${mode}_${w}_$e.txt
        XENV=""; case $e in *_lb) XENV="LTSBFILE=${LTSB:?LTSB must name the LTSB file}";; esac; case $e in *chk*) XENV="$XENV LWE11CHECK=1";; esac
        env -u SYMFILE -u LTSFILE -u PROBES -u ALARM -u LWE11OFF -u LWE11NOSKIP -u LWE11NOGSKIP -u LWE11NOBULK -u LWE11NOTIESKIP -u LWE11OLDLH -u LWE11THR -u LWE11CHECK -u LWE11NOFASTSPLIT -u LWE11NOFUSE -u LWE11GENDUMP -u LTSBFILE $XENV LTSHFILE=$P/sym.ltsh timeout 240 nice -n 10 ${ENG[$e]} $inst > $out 2>&1
        st=$(grep -c STOPPED $out); dn=$(grep -c '^DONE' $out)
        v=$(timeout 300 nice -n 10 $H/pin verify prep.txt $P/inst.txt $P/key.txt $s $mode $h $w < $out 2>&1 | tail -1)
        sig=$(grep -E '^(LEVEL|SOLUTION|LBPRUNE)' $out | sha256sum | cut -c1-12)
        [ -z "$ref" ] && [ "$st" = 0 ] && ref=$sig
        same=$([ "$st" != 0 ] && echo partial || ([ "$sig" = "$ref" ] && echo same || echo DIFF))
        lb=$(awk '/^LBPRUNE/ {n=0; for (i = 2; i <= NF; i++) {split($i, a, ":"); n += a[2]}; print n}' $out)
        echo "$TAG s$s m$mode $w $e done=$dn stopped=$st levels=$same${lb:+ lbprune=$lb} | $v"
      done
      echo "   [$info]"
      rm -f $inst
    done
  done
done
