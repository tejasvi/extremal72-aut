#!/bin/bash
# runjobs.sh JOBFILE NPROC : box-side resumable sample runner. JOBFILE lines: "CODE SPL NPART PART" (CODE = run dir
# name under <HOME>/struct/runs). Output <HOME>/struct/samples/CODE/sSPLnNPART_pPART.{log,time}; parts with DONE are skipped.
set -u
R=<HOME>/struct/runs; O=<HOME>/struct/samples; export TMPDIR=<HOME>/struct/tmp; mkdir -p $TMPDIR
cat "$1" | xargs -P "$2" -L 1 sh -c '
  c=$0; s=$1; n=$2; p=$3; d='"$O"'/$c; mkdir -p $d; f=$d/s${s}n${n}_p$p
  if [ -s $f.log ] && grep -q "^DONE" $f.log && ! grep -q STOPPED $f.log; then exit 0; fi
  LTSHFILE='"$R"'/$c/sym.ltsh nice -n 10 /usr/bin/time -f "user %U wall %e maxrss %M" '"$R"'/frozen3/lwe10 '"$R"'/$c/inst.txt $s $n $p > $f.log.tmp 2> $f.time && mv $f.log.tmp $f.log'
echo "ALLDONE $1"
