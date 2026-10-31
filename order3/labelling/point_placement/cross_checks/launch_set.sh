#!/bin/bash
# usage: launch_set.sh SETNAME INPUTFILE NCHUNKS  -- runs gtest4 E and csp5p COUNT=1 E on every chunk (2*NCHUNKS procs)
cd "$(dirname "$0")"
S=$1; IN=$2; NC=$3
mkdir -p runs/$S && cd runs/$S
split -n l/$NC -d -a 3 ../../$IN ch_
for f in ch_???; do
  ( nice -n 10 ../../gt4src/gtest4 E $f > $f.gt4 2>&1 ; echo done >> $f.gt4.fin ) &
  ( COUNT=1 nice -n 10 ../../../prod_v1/csp5p 24 E $f ../../../prod_v1/octdod.txt > $f.csp 2>&1 ; echo done >> $f.csp.fin ) &
done
wait
echo ALLDONE > ALLDONE
