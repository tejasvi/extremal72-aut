#!/bin/bash
cd "${WORKDIR:-.}"
export OMP_NUM_THREADS=16
THRESH=14 NDIVES=20 SEED=31337 nice -n 10 ./tester > t14.out 2> t14.err
THRESH=12 NTESTS=40 SEED=5551212 nice -n 10 ./planted2 > p12.out 2> p12.err
echo done > chainB.done
