#!/bin/bash
# cmpbin.sh BINA BINB JOBFILE : each job line "tag|ENV=.. ENV=..|args"; runs both binaries sequentially (1 core), prints
# user seconds and the hash of LEVEL/DONE/SOL/LBPRUNE lines.
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
A=$1; B=$2; TIMEFORMAT="%U"
while IFS='|' read -r tag envs args; do
  [ -z "$tag" ] && continue
  r=""
  for bin in $A $B; do
    t=$( { time env $envs nice -n 10 $bin $args > tmp/cmp_$tag.log 2>/dev/null; } 2>&1 )
    h=$(grep -E '^LEVEL|^DONE|^SOL|^LBPRUNE' tmp/cmp_$tag.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-12)
    r="$r $t $h"
  done
  set -- $r; echo "$tag A $1 $2 B $3 $4 $([ "$2" = "$4" ] && echo IDENTICAL || echo DIFFER)"
done < $3
