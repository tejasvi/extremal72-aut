#!/bin/bash
# Box-side checks before a run with lwe11b5 (AVX2 twin of rc11): build lwe11b (keeps an existing build if 'keep' is given), verify input hashes
# and the frozen preparation sources, compare the probe estimate with PLAN.txt, and run one small part (17 of 200000):
#  - without LTSBFILE with LWE8 (default ../frozen/lwe8, override with LWE8=path) and lwe11b: LEVEL/DONE/SOLUTION identical;
#  - for an LTSB package (PLAN.txt line "LTSBFILE <name>"; the file must exist and be listed in INPUTS.sha256; a sym.ltsb
#    without that line is refused): with LTSBFILE with the prototype lwe10b (c2struct, source lwe10b.c here; binary LWE10B,
#    default ./lwe10b, built from lwe10b.c if missing) and lwe11b: LEVEL/DONE/SOLUTION/LBPRUNE identical.
# The probe of an LTSB package uses LTSBFILE (PLAN.txt's PROBE_LTS must then include the bit-granular test).
# Usage: check_box.sh CODEDIR [keep]      (layout as in c2explore runs2/: CODEDIR next to this directory's parent)
set -u
FROZ=$(cd "$(dirname "$0")" && pwd); CODEDIR=$(cd "$1" && pwd); OLD=$FROZ/../frozen
export TMPDIR=${TMPDIR:-$CODEDIR}
LWE8=${LWE8:-$OLD/lwe8}; LWE10B=${LWE10B:-$FROZ/lwe10b}
if [ "${2:-}" != "keep" ] || [ ! -x $FROZ/lwe11b ]; then ( cd $FROZ && ./build.sh > /dev/null ) || { echo "BUILD FAILED"; exit 1; }; fi
[ -x $LWE8 ] || ( cd $(dirname $LWE8) && ./build.sh > /dev/null ) || { echo "LWE8 BUILD FAILED"; exit 1; }
grep lwe11b $FROZ/BUILD.sha256; sha256sum $FROZ/lwe11b | awk '{print "binary in use:", $1}'
if [ -f $CODEDIR/INPUTS.sha256 ]; then
  ( cd $CODEDIR && sha256sum -c --quiet <(grep -v frozen/ INPUTS.sha256) ) && echo "inputs OK"
  ( cd $CODEDIR/.. && sha256sum -c --quiet <(grep frozen/ $CODEDIR/INPUTS.sha256) ) && echo "frozen sources OK"
fi
LBN=$(grep '^LTSBFILE ' $CODEDIR/PLAN.txt | awk '{print $2}'); LB=""
if [ -n "$LBN" ]; then
  [ -f $CODEDIR/$LBN ] || { echo "LTSB FILE $LBN MISSING"; exit 1; }; LB="LTSBFILE=$CODEDIR/$LBN"
  sha256sum $CODEDIR/$LBN | awk '{print "LTSB package, LTSBFILE in use:", $1}'
  if [ -f $CODEDIR/INPUTS.sha256 ]; then grep -q " $LBN\$" $CODEDIR/INPUTS.sha256 && echo "LTSBFILE listed in INPUTS.sha256" || echo "LTSBFILE NOT LISTED IN INPUTS.sha256"; fi
  [ -x $LWE10B ] || gcc -pipe -O3 -march=x86-64-v3 -o $LWE10B $FROZ/lwe10b.c || { echo "LWE10B BUILD FAILED"; exit 1; }
elif [ -f $CODEDIR/sym.ltsb ]; then echo "sym.ltsb PRESENT BUT PLAN.txt HAS NO LTSBFILE LINE"; exit 1
else echo "not an LTSB package"; fi
EXP=$(grep '^PROBE_LTS ' $CODEDIR/PLAN.txt | awk '{print $2}')
GOT=$(env PROBES=20000 LTSHFILE=$CODEDIR/sym.ltsh $LB $FROZ/lwe11b $CODEDIR/inst.txt | tail -1 | awk '{print $NF}')
echo "probe estimate expected $EXP got $GOT"; [ "$EXP" = "$GOT" ] && echo "PROBE OK" || echo "PROBE MISMATCH"
SPL=$(grep '^SPLIT_LEVEL ' $CODEDIR/PLAN.txt | awk '{print $2}')
A=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $LWE8 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | sha256sum)
B=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $FROZ/lwe11b $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | sha256sum)
[ "$A" = "$B" ] && echo "LWE8/LWE11B IDENTICAL (part 17 of 200000, without LTSBFILE)" || echo "LWE8/LWE11B DIFFER"
if [ -n "$LB" ]; then
  A=$(env LTSHFILE=$CODEDIR/sym.ltsh $LB nice -n 10 $LWE10B $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE|^LBPRUNE' | sed 's/time [0-9]*s//' | sha256sum)
  B=$(env LTSHFILE=$CODEDIR/sym.ltsh $LB nice -n 10 $FROZ/lwe11b $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE|^LBPRUNE' | sed 's/time [0-9]*s//' | sha256sum)
  [ "$A" = "$B" ] && echo "LWE10B/LWE11B IDENTICAL WITH LTSBFILE (part 17 of 200000)" || echo "LWE10B/LWE11B DIFFER WITH LTSBFILE"
fi
