#!/bin/bash
# Box-side checks before a run with lwe11 rc14g (y15-lb only): build lwe11 (keeps an existing build if 'keep' is given), verify input hashes
# and the frozen preparation sources, compare the probe estimate with PLAN.txt, and run one small part (17 of 200000):
#  - without LTSBFILE with LWE8 (default ../frozen/lwe8, override with LWE8=path) and lwe11: LEVEL/DONE/SOLUTION identical;
#  - for an LTSB package (PLAN.txt line "LTSBFILE <name>"; the file must exist and be listed in INPUTS.sha256; a sym.ltsb
#    without that line is refused): with LTSBFILE with the prototype lwe10b (c2struct, source lwe10b.c here; binary LWE10B,
#    default ./lwe10b, built from lwe10b.c if missing) and lwe11: LEVEL/DONE/SOLUTION/LBPRUNE identical.
# The probe of an LTSB package uses LTSBFILE (PLAN.txt's PROBE_LTS must then include the bit-granular test).
# rc13 and rc14 kits (auditc3 F-C10): every identity output must contain a DONE line, and any MISMATCH, MISSING or DIFFER verdict
# makes the script end with "CHECK_BOX FAILED" and exit status 1; "CHECK_BOX PASSED" and status 0 otherwise.  The other
# output lines are the same as in the rc11 kit.
# Usage: check_box.sh CODEDIR [keep]      (layout as in c2explore runs2/: CODEDIR next to this directory's parent)
set -u
FROZ=$(cd "$(dirname "$0")" && pwd); CODEDIR=$(cd "$1" && pwd); OLD=$FROZ/../frozen
export TMPDIR=${TMPDIR:-$CODEDIR}
LWE8=${LWE8:-$OLD/lwe8}; LWE10B=${LWE10B:-$FROZ/lwe10b}; FAIL=0
bad() { echo "$1"; FAIL=$((FAIL + 1)); }
if [ "${2:-}" != "keep" ] || [ ! -x $FROZ/lwe11 ]; then ( cd $FROZ && ./build.sh > /dev/null ) || { echo "BUILD FAILED"; echo "CHECK_BOX FAILED"; exit 1; }; fi
[ -x $LWE8 ] || ( cd $(dirname $LWE8) && ./build.sh > /dev/null ) || { echo "LWE8 BUILD FAILED"; echo "CHECK_BOX FAILED"; exit 1; }
grep lwe11 $FROZ/BUILD.sha256; sha256sum $FROZ/lwe11 | awk '{print "binary in use:", $1}'
if [ -f $CODEDIR/INPUTS.sha256 ]; then
  ( cd $CODEDIR && sha256sum -c --quiet <(grep -v frozen/ INPUTS.sha256) ) && echo "inputs OK" || bad "INPUTS MISMATCH"
  if grep -q frozen/ $CODEDIR/INPUTS.sha256; then
    ( cd $CODEDIR/.. && sha256sum -c --quiet <(grep frozen/ $CODEDIR/INPUTS.sha256) ) && echo "frozen sources OK" || bad "FROZEN SOURCES MISMATCH"
  else echo "no frozen sources listed in INPUTS.sha256"; fi
else bad "INPUTS.sha256 MISSING"; fi
LBN=$(grep '^LTSBFILE ' $CODEDIR/PLAN.txt | awk '{print $2}'); LB=""
if [ -n "$LBN" ]; then
  [ -f $CODEDIR/$LBN ] || { echo "LTSB FILE $LBN MISSING"; echo "CHECK_BOX FAILED"; exit 1; }; LB="LTSBFILE=$CODEDIR/$LBN"
  sha256sum $CODEDIR/$LBN | awk '{print "LTSB package, LTSBFILE in use:", $1}'
  if [ -f $CODEDIR/INPUTS.sha256 ]; then grep -q " $LBN\$" $CODEDIR/INPUTS.sha256 && echo "LTSBFILE listed in INPUTS.sha256" || bad "LTSBFILE NOT LISTED IN INPUTS.sha256"; fi
  [ -x $LWE10B ] || gcc -pipe -O3 -march=x86-64-v3 -o $LWE10B $FROZ/lwe10b.c || { echo "LWE10B BUILD FAILED"; echo "CHECK_BOX FAILED"; exit 1; }
elif [ -f $CODEDIR/sym.ltsb ]; then echo "sym.ltsb PRESENT BUT PLAN.txt HAS NO LTSBFILE LINE"; echo "CHECK_BOX FAILED"; exit 1
else echo "not an LTSB package"; fi
EXP=$(grep '^PROBE_LTS ' $CODEDIR/PLAN.txt | awk '{print $2}')
GOT=$(env PROBES=20000 LTSHFILE=$CODEDIR/sym.ltsh $LB $FROZ/lwe11 $CODEDIR/inst.txt | tail -1 | awk '{print $NF}')
echo "probe estimate expected $EXP got $GOT"
if [ -z "$EXP" ] || [ -z "$GOT" ]; then bad "PROBE MISSING"; elif [ "$EXP" = "$GOT" ]; then echo "PROBE OK"; else bad "PROBE MISMATCH"; fi
SPL=$(grep '^SPLIT_LEVEL ' $CODEDIR/PLAN.txt | awk '{print $2}')
same() {   # same OK_LINE DIFFER_LINE MISSING_LINE OUT_A OUT_B : both filtered outputs need a DONE line and must be identical
  if ! grep -q '^DONE' <<< "$4" || ! grep -q '^DONE' <<< "$5"; then bad "$3"
  elif [ "$(sha256sum <<< "$4")" = "$(sha256sum <<< "$5")" ]; then echo "$1"; else bad "$2"; fi; }
A=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $LWE8 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//')
B=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $FROZ/lwe11 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//')
same "LWE8/LWE11 IDENTICAL (part 17 of 200000, without LTSBFILE)" "LWE8/LWE11 DIFFER" "LWE8/LWE11 MISSING (an identity run printed no DONE line)" "$A" "$B"
if [ -n "$LB" ]; then
  A=$(env LTSHFILE=$CODEDIR/sym.ltsh $LB nice -n 10 $LWE10B $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE|^LBPRUNE' | sed 's/time [0-9]*s//')
  B=$(env LTSHFILE=$CODEDIR/sym.ltsh $LB nice -n 10 $FROZ/lwe11 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE|^LBPRUNE' | sed 's/time [0-9]*s//')
  same "LWE10B/LWE11 IDENTICAL WITH LTSBFILE (part 17 of 200000)" "LWE10B/LWE11 DIFFER WITH LTSBFILE" "LWE10B/LWE11 MISSING WITH LTSBFILE (an identity run printed no DONE line)" "$A" "$B"
fi
if [ $FAIL -eq 0 ]; then echo "CHECK_BOX PASSED"; exit 0; else echo "CHECK_BOX FAILED ($FAIL problem(s))"; exit 1; fi
