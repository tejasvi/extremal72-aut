#!/bin/bash
# runpart_s.sh INST LTSH SPL NPART PART OUTPREFIX : one sample part with lwe10s (raw-index split; paired comparisons)
D=<HOME>/c72/c2opt/struct; export TMPDIR=$D/tmp
LTSHFILE=$2 nice -n 10 /usr/bin/time -f "user %U wall %e maxrss %M" $D/src/lwe10s $1 $3 $4 $5 > $6.log 2> $6.time
echo "done $6"
