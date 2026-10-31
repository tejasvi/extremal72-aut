#!/bin/bash
# runpart.sh BIN CODE SPL NPART PART OUTPREFIX : run one part, LEVEL/DONE lines to OUT.log, user/wall/maxrss to OUT.time
set -u
BIN=$1; CODE=$2; SPL=$3; NPART=$4; PART=$5; OUT=$6
export TMPDIR=<HOME>/c72/c2opt/alg/tmp
D=<HOME>/c72/explore/runs2/$CODE
LTSHFILE=$D/sym.ltsh /usr/bin/time -f "%U %e %M" -o $OUT.time nice -n 10 $BIN $D/inst.txt $SPL $NPART $PART > $OUT.log 2> $OUT.err
