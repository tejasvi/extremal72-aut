#!/bin/bash
# Run parts FIRST..LAST of a split run for one code directory with lwe11 rc14g for package y40 (resumable: parts with a DONE line are skipped).
# Uses CODEDIR/sym.ltsh (LTSHFILE). Bit-granular LTS is a fixed package property: PLAN.txt line "LTSBFILE <name>"
# (file in CODEDIR, listed in INPUTS.sha256). It refuses to run if the named file is missing, or if a sym.ltsb exists
# without that line, so LB and non-LB parts can never mix within a package.
# Usage: run_parts.sh CODEDIR SPL NPART FIRST LAST NPROC        (TMPDIR must be set by the caller)
set -u
CODEDIR=$(cd "$1" && pwd); SPL=$2; NPART=$3; FIRST=$4; LAST=$5; NPROC=$6
BIN=$(cd "$(dirname "$0")" && pwd)/lwe11
LBN=$(grep '^LTSBFILE ' "$CODEDIR/PLAN.txt" 2>/dev/null | awk '{print $2}'); LB=""
if [ -n "$LBN" ]; then [ -f "$CODEDIR/$LBN" ] || { echo "PLAN.txt names LTSBFILE $LBN but $CODEDIR/$LBN is missing: refusing"; exit 1; }; LB="LTSBFILE=$CODEDIR/$LBN"
elif [ -f "$CODEDIR/sym.ltsb" ]; then echo "$CODEDIR/sym.ltsb exists but PLAN.txt has no LTSBFILE line: refusing"; exit 1; fi
mkdir -p "$CODEDIR/parts"
seq $FIRST $LAST | xargs -P $NPROC -I{} sh -c "f=$CODEDIR/parts/p{}.log; if [ -s \$f ] && grep -q '^DONE' \$f && ! grep -q STOPPED \$f; then exit 0; fi; LTSHFILE=$CODEDIR/sym.ltsh $LB nice -n 10 $BIN $CODEDIR/inst.txt $SPL $NPART {} > \$f.tmp 2>&1 && mv \$f.tmp \$f"
echo "ALLDONE $FIRST..$LAST"
