#!/bin/bash
# Box-side checks before a run with lwe11b: build lwe11b (keeps an existing build if 'keep' is given), verify input hashes
# and the frozen preparation sources, compare the lwe11b probe estimate with PLAN.txt, and run one small part with both
# LWE8 (default ../frozen/lwe8, override with LWE8=path) and lwe11b: LEVEL/DONE/SOLUTION lines must be identical.
# Usage: check_box.sh CODEDIR [keep]      (layout as in c2explore runs2/: CODEDIR next to this directory's parent)
set -u
FROZ=$(cd "$(dirname "$0")" && pwd); CODEDIR=$(cd "$1" && pwd); OLD=$FROZ/../frozen
export TMPDIR=${TMPDIR:-$CODEDIR}
LWE8=${LWE8:-$OLD/lwe8}
if [ "${2:-}" != "keep" ] || [ ! -x $FROZ/lwe11b ]; then ( cd $FROZ && ./build.sh > /dev/null ) || { echo "BUILD FAILED"; exit 1; }; fi
[ -x $LWE8 ] || ( cd $(dirname $LWE8) && ./build.sh > /dev/null ) || { echo "LWE8 BUILD FAILED"; exit 1; }
grep lwe11b $FROZ/BUILD.sha256; sha256sum $FROZ/lwe11b | awk '{print "binary in use:", $1}'
if [ -f $CODEDIR/INPUTS.sha256 ]; then
  ( cd $CODEDIR && sha256sum -c --quiet <(grep -v frozen/ INPUTS.sha256) ) && echo "inputs OK"
  ( cd $CODEDIR/.. && sha256sum -c --quiet <(grep frozen/ $CODEDIR/INPUTS.sha256) ) && echo "frozen sources OK"
fi
EXP=$(grep '^PROBE_LTS ' $CODEDIR/PLAN.txt | awk '{print $2}')
GOT=$(PROBES=20000 LTSHFILE=$CODEDIR/sym.ltsh $FROZ/lwe11b $CODEDIR/inst.txt | tail -1 | awk '{print $NF}')
echo "probe estimate expected $EXP got $GOT"; [ "$EXP" = "$GOT" ] && echo "PROBE OK" || echo "PROBE MISMATCH"
SPL=$(grep '^SPLIT_LEVEL ' $CODEDIR/PLAN.txt | awk '{print $2}')
A=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $LWE8 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | sha256sum)
B=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $FROZ/lwe11b $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | sha256sum)
[ "$A" = "$B" ] && echo "LWE8/LWE11B IDENTICAL (part 17 of 200000)" || echo "LWE8/LWE11B DIFFER"
