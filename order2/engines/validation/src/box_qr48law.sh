#!/bin/bash
# box_qr48law.sh : rc10/lwe11b4 LAWFILE control on math's QR48 instance (N 44; proven law A_8/2 = C + <l,x>, Lz 10;
# every extremal solution satisfies it). 20 parts at split 5 (<= Lz). Per part: lwe11b3 (baseline), lwe11b4 without
# LAWFILE, with LAWFILE in count mode, in prune mode, and in prune mode with LWE11CHECK. At most 20 processes.
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; Q=<HOME>/alg/qr48; O=logs/qr48law; mkdir -p $O; ulimit -v 4000000
gcc -pipe -O3 -march=x86-64-v3 -o bin/lwe11b4 src/lwe11b4.c || exit 1
sha256sum bin/lwe11b4 bin/lwe11b3 src/lwe11b4.c $Q/* > $O/FILES.sha256
{ for p in $(seq 0 19); do for m in b3 none count prune; do echo "$m $p"; done; done; for p in $(seq 0 19); do echo "chk $p"; done; } > $O/jobs.txt
cat $O/jobs.txt | xargs -P 20 -L 1 sh -c 'm=$0; p=$1; Q=<HOME>/alg/qr48; O=logs/qr48law/${m}_$p; ulimit -v 4000000
  case $m in b3) nice -n 10 bin/lwe11b3 $Q/inst.txt 5 20 $p > $O.log 2> $O.err ;;
    none) nice -n 10 bin/lwe11b4 $Q/inst.txt 5 20 $p > $O.log 2> $O.err ;;
    count) LAWFILE=$Q/qr48.law LAWCOUNT=1 nice -n 10 bin/lwe11b4 $Q/inst.txt 5 20 $p > $O.log 2> $O.err ;;
    prune) LAWFILE=$Q/qr48.law nice -n 10 bin/lwe11b4 $Q/inst.txt 5 20 $p > $O.log 2> $O.err ;;
    chk) LAWFILE=$Q/qr48.law LWE11CHECK=1 nice -n 10 bin/lwe11b4 $Q/inst.txt 5 20 $p > $O.log 2> $O.err ;;
  esac'
date -u > $O/DONE.txt
