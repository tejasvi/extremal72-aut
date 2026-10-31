#!/bin/bash
# Re-run the audit coverage checker on every completed code (single core, nice 10; each check < 5 min).
# usage: cov_all.sh [code ...]   (default: every fleet package with a COMPLETE file + explore's completed codes)
# Prefix references (prefix_<code>.txt) are made with the own lwe8 build when missing.
set -u
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
cd <HOME>/c72/audit/c2audit/c3 || exit 1
PY="nice -n 10 <HOME>/c72/venv/bin/python -I"
FR=<HOME>/c72/fleet/results
ST=<HOME>/c72/c2opt/struct/runs
E=<HOME>/c72/explore
R=$E/runs2
# approved fleet engines (binary sha256): rc7, lwe11b, rc9, lwe11b3 (approved 10-21); rc11, lwe11b5 (LTSB packages, pass-conditional per the project's gate)
RC7=645a9f5c7cc831817e131059846714c561c0c9484728632744667439061255b0
LWE11B=2fdae1bb9bc924e2dc54be91482d64f5ae89e3fa1406bb1b0aa69a5b1757b941
RC9=dfbad27a7e9d69668eb8530226a6afa16fcc6925236b7c77529e18b7e4514424
LWE11B3=3eddc9a884ef9fae1ad953e96a4292098524e6304d7c2c99908dd00f2ae1e3f3
RC11=cb04bfa878225611d671c158df0d6bdf36bca405e2a19bf87ba9826ea5259455        # rc11 (LTSB), frozen 10-21 21:10 UTC
LWE11B5=268d592dbec3e4da07672ade5701529543425fb3cc21ffcba8e0916afbae3348     # lwe11b5 (LTSB, AVX2)
RC13=2cd44f916033e388a9f8cca85bf0487ba0389212b6700001339bb85c92aa4200        # rc13 (drop-in for rc11), frozen 10-22
LWE11B7=ab9f2df8c3823a3406ce045281e920221e7bc2294402c229f6ee44a636c39464     # lwe11b7 (drop-in for lwe11b5)
RC14=ed00eb07620323370f36385a52fc27241068438ea6d757ff5ed14918b4386664        # rc14 (rc13 + direct-table cap)
# rc14g binaries are package-specific: each is allowed for its own package only
declare -A RC14G=( [y40]=8d6b797215e4679146a2dc86c58370fee8cae3d53cb4ce7e62552a1a5d1929b8 [y12-lb2]=7eeb6552a26bf15c62847685c3f46a3dccd6c87824ae6d70ef44b3b837ea2c9a [y15-lb]=f670798e1f52e38856fa3e4cc5666f0a325fd2b8975bc69c9b54703bcd115359 )
prefix() {  # prefix CODE PKGDIR [INST]
  local c=$1 P=$2 I=${3:-$2/inst.txt}
  [ -s prefix_$c.txt ] && return
  local SPL; SPL=$(awk '$1=="SPLIT_LEVEL"{print $2}' $P/PLAN.txt)
  local LBF; LBF=$(awk '$1=="LTSBFILE"{print $2}' $P/PLAN.txt)
  if [ -n "$LBF" ]; then   # bit-granular LTS package (rc11, PLAN 'LTSBFILE name'): reference = own build of lwe10b.c + LTSBFILE
    env -i PATH=/usr/bin:/bin TMPDIR=$TMPDIR LTSHFILE=$P/sym.ltsh LTSBFILE=$P/$LBF timeout 540 nice -n 10 ./lwe10b_ref $I $SPL 2147483647 0 > prefix_$c.txt 2>&1
  else
    env -u SYMFILE -u LTSFILE -u PROBES -u ALARM -u LTSBFILE LTSHFILE=$P/sym.ltsh timeout 540 nice -n 10 ./lwe8_ref $I $SPL 2147483647 0 > prefix_$c.txt 2>&1
  fi
}
fleet() {  # fleet PKG
  local p=$1 P=$ST/$1
  [ -d $P ] || P=$R/$1
  prefix $p $P
  timeout 280 $PY cov_c2.py --pkg $P --parts $FR/$p/parts --fleet $FR/$p --engines $RC7,$LWE11B,$RC9,$LWE11B3,$RC11,$LWE11B5,$RC13,$LWE11B7,$RC14${RC14G[$p]:+,${RC14G[$p]}} --prefix prefix_$p.txt --report cov_$p.txt > /dev/null
}
c2e() {  # c2e CODE PARTSDIR [extra args]; lwe8 reruns of explore's own runs land in fleet/results_xc2e/CODE
  local c=$1 d=$2; shift 2
  prefix $c $R/$c
  local XC=""; [ -d <HOME>/c72/fleet/results_xc2e/$c ] && XC="--xcheck <HOME>/c72/fleet/results_xc2e/$c"
  timeout 280 $PY cov_c2.py --pkg $R/$c --parts $R/$c/$d --prefix prefix_$c.txt --report cov_$c.txt $XC "$@" > /dev/null
}
one() {
  case $1 in
    y39) timeout 280 $PY cov_c2.py --pkg $E/runs/y39 --parts $E/runs/y39 --npart 2000 --split 3 --inputs-root $E \
           --inst $E/inst/y39_ginv.txt --prefix prefix_y39.txt --report cov_y39.txt --allow-sym > /dev/null ;;
    y8) c2e y8 parts ;;
    y22) c2e y22 parts_hostB ;;
    y23) c2e y23 parts_hostB ;;
    y4) c2e y4 parts_hostC --alt $R/y4/parts_local ;;
    y5b) c2e y5b parts_hostC ;;
    y1b) c2e y1b parts_all --alt $R/y1b/parts_hostB --alt $R/y1b/parts_hostC --alt $R/y1b/parts_local ;;
    y29) c2e y29 parts_all --alt $R/y29/parts_hostK/parts --alt $R/y29/parts_hostL/parts ;;
    *) fleet $1 ;;
  esac
  printf '%-5s %s | %s\n' $1 "$(grep -E '^VERDICT' cov_$1.txt)" "$(grep -E '^SYMFILE' cov_$1.txt)"
}
if [ $# -gt 0 ]; then L="$*"; else
  L="y39 y8 y22 y23 y4 y5b y1b y29"
  for f in $FR/*/COMPLETE; do L="$L $(basename $(dirname $f))"; done
fi
for c in $L; do one $c; done
