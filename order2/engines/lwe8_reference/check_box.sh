#!/bin/bash
# Box-side checks before a run: rebuild lwe8 from the frozen source, verify input hashes, compare a probe estimate
# with the value recorded in CODEDIR/PLAN.txt.  Usage: check_box.sh CODEDIR
set -u
FROZ=$(cd "$(dirname "$0")" && pwd); CODEDIR=$(cd "$1" && pwd)
export TMPDIR=${TMPDIR:-$CODEDIR}
( cd $FROZ && ./build.sh > /dev/null ) || { echo "BUILD FAILED"; exit 1; }
grep lwe8.c $FROZ/BUILD.sha256
( cd $CODEDIR && sha256sum -c --quiet <(grep -v frozen/ INPUTS.sha256) ) && echo "inputs OK"
( cd $CODEDIR/.. && sha256sum -c --quiet <(grep frozen/ $CODEDIR/INPUTS.sha256) ) && echo "frozen sources OK"
EXP=$(grep '^PROBE_LTS ' $CODEDIR/PLAN.txt | awk '{print $2}')
GOT=$(PROBES=20000 LTSHFILE=$CODEDIR/sym.ltsh $FROZ/lwe8 $CODEDIR/inst.txt | tail -1 | awk '{print $NF}')
echo "probe estimate expected $EXP got $GOT"; [ "$EXP" = "$GOT" ] && echo "PROBE OK" || echo "PROBE MISMATCH"
