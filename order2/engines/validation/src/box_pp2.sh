#!/bin/bash
# box_pp2.sh : AVX2 build variants on hostM (<CPU>), loaded as in box_pp.sh: 16 processes pinned to both SMT threads of
# 8 cores (cpus 40-47 + 152-159), each core running two copies of the same binary on y18c part 17 of 10000.
# lwe11b3 = production build (gcc 14.2, x86-64-v3); m3base/m3tz3/m3tz2 = gcc 15.2 x86-64-v3 / -mtune=znver3 / -mtune=znver2.
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/pp2; ulimit -v 4000000
run() { e=$1; cpu=$2; O=logs/pp2/${e}_c$cpu; TIMEFORMAT="%U %R"
  { time LTSHFILE=struct/y18c/sym.ltsh nice -n 10 taskset -c $cpu bin/$e struct/y18c/inst.txt 3 10000 17 > $O.log 2> $O.err ; } 2> $O.time; }
i=0
for e in lwe11b3 m3base m3tz3 m3tz2 lwe11b3 m3base m3tz3 m3tz2; do c=$((40 + i)); run $e $c & run $e $((c + 112)) & i=$((i + 1)); done
wait; date -u > logs/pp2/PP2_DONE.txt
