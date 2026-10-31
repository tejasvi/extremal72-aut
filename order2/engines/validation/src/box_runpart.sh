#!/bin/bash
# box_runpart.sh BIN CODE SPL NPART PART OUT : one part on the box (nice 10, ulimit -v 4 GB); LEVEL/DONE to OUT.log, user/wall/rss to OUT.time
B=$1; C=$2; SPL=$3; NP=$4; P=$5; O=$6
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; D=<HOME>/alg/explore/runs2/$C
ulimit -v 4000000
[ -s $O.log ] && grep -q '^DONE' $O.log && exit 0
LTSHFILE=$D/sym.ltsh /usr/bin/time -f "%U %e %M" -o $O.time nice -n 10 $B $D/inst.txt $SPL $NP $P > $O.log 2> $O.err
