#!/bin/bash
# box_qr48plain.sh : plain solution set of the QR48 key-control instance (struct qr48keyb flag 'qr', full mode), no
# symmetry, 20 parts at split 5 with lwe11b3, at most 20 processes. Output logs/qr48plain/p<k>.log
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/qr48plain
seq 0 19 | xargs -P 20 -I{} sh -c 'ulimit -v 4000000; nice -n 10 bin/lwe11b3 qr48lb/qr48k_full_qr.txt 5 20 {} > logs/qr48plain/p{}.log 2> logs/qr48plain/p{}.err'
date -u > logs/qr48plain/DONE.txt
