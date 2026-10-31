#!/bin/bash
# Run parts FIRST..LAST of a split run for one code directory (resumable: parts with a DONE line are skipped).
# Usage: run_parts.sh CODEDIR SPL NPART FIRST LAST NPROC        (TMPDIR must be set by the caller)
set -u
CODEDIR=$(cd "$1" && pwd); SPL=$2; NPART=$3; FIRST=$4; LAST=$5; NPROC=$6
BIN=$(cd "$(dirname "$0")" && pwd)/lwe8
mkdir -p "$CODEDIR/parts"
seq $FIRST $LAST | xargs -P $NPROC -I{} sh -c "f=$CODEDIR/parts/p{}.log; if [ -s \$f ] && grep -q '^DONE' \$f && ! grep -q STOPPED \$f; then exit 0; fi; LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 $BIN $CODEDIR/inst.txt $SPL $NPART {} > \$f.tmp 2>&1 && mv \$f.tmp \$f"
echo "ALLDONE $FIRST..$LAST"
