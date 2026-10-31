#!/bin/bash
# paired.sh CODE SPL NPART PART : lwe10 (frozen3 build) and frozen lwe11 started together on the same part; logs/paired/
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp; mkdir -p logs/paired
src/runpart.sh bin/lwe10 $1 $2 $3 $4 logs/paired/${1}_p$4_lwe10 &
src/runpart.sh bin/lwe11rc6 $1 $2 $3 $4 logs/paired/${1}_p$4_rc6 &
wait
