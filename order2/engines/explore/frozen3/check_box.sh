#!/bin/bash
# Box-side checks before a run with lwe10: build lwe10 (keeps an existing native build if 'keep' is given), verify input
# hashes and the frozen preparation sources, compare the lwe10 probe estimate with PLAN.txt, and run one small part
# with both frozen/lwe8 and lwe10: the LEVEL lines must be identical.  Usage: check_box.sh CODEDIR [keep]
set -u
FROZ=$(cd "$(dirname "$0")" && pwd); CODEDIR=$(cd "$1" && pwd); OLD=$FROZ/../frozen
export TMPDIR=${TMPDIR:-$CODEDIR}
if [ "${2:-}" != "keep" ] || [ ! -x $FROZ/lwe10 ]; then ( cd $FROZ && ./build.sh > /dev/null ) || { echo "BUILD FAILED"; exit 1; }; fi
[ -x $OLD/lwe8 ] || ( cd $OLD && ./build.sh > /dev/null ) || { echo "LWE8 BUILD FAILED"; exit 1; }
grep lwe10 $FROZ/BUILD.sha256; sha256sum $FROZ/lwe10 | awk '{print "binary in use:", $1}'
( cd $CODEDIR && sha256sum -c --quiet <(grep -v frozen/ INPUTS.sha256) ) && echo "inputs OK"
( cd $CODEDIR/.. && sha256sum -c --quiet <(grep frozen/ $CODEDIR/INPUTS.sha256) ) && echo "frozen sources OK"
EXP=$(grep '^PROBE_LTS ' $CODEDIR/PLAN.txt | awk '{print $2}')
GOT=$(PROBES=20000 LTSHFILE=$CODEDIR/sym.ltsh $FROZ/lwe10 $CODEDIR/inst.txt | tail -1 | awk '{print $NF}')
echo "probe estimate expected $EXP got $GOT"; [ "$EXP" = "$GOT" ] && echo "PROBE OK" || echo "PROBE MISMATCH"
SPL=$(grep '^SPLIT_LEVEL ' $CODEDIR/PLAN.txt | awk '{print $2}')
A=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $OLD/lwe8 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | sha256sum)
B=$(LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $FROZ/lwe10 $CODEDIR/inst.txt $SPL 200000 17 | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | sha256sum)
[ "$A" = "$B" ] && echo "LWE8/LWE10 IDENTICAL (part 17 of 200000)" || echo "LWE8/LWE10 DIFFER"
