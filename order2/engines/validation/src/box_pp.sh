#!/bin/bash
# box_pp.sh : loaded-throughput sample on hostM (famF, <CPU>). 16 processes pinned to the two SMT threads of 8 cores
# (one CCD, cores 40-47 = cpus 40-47 + 152-159), two copies of the same engine and part per core, so every process
# shares its core as under full load. Parts: y18c and y16b part 17 of 10000 (split 3), as fleet's bench references.
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/pp; ulimit -v 4000000
run() { e=$1; p=$2; cpu=$3; O=logs/pp/${p}_${e}_c$cpu; TIMEFORMAT="%U %R"
  { time LTSHFILE=struct/$p/sym.ltsh nice -n 10 taskset -c $cpu bin/$e struct/$p/inst.txt 3 10000 17 > $O.log 2> $O.err ; } 2> $O.time; }
i=0
for job in "lwe11b y18c" "lwe11b y18c" "lwe11b3 y18c" "lwe11b3 y18c" "lwe11b y16b" "lwe11b y16b" "lwe11b3 y16b" "lwe11b3 y16b"; do
  c=$((40 + i)); run $job $c & run $job $((c + 112)) & i=$((i + 1)); done
wait; date -u > logs/pp/PP_DONE.txt
