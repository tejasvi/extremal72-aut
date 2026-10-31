#!/bin/bash
cd "${WORKDIR:-.}"
export OMP_NUM_THREADS=16
THRESH=16 NDIVES=60 SEED=20261018 nice -n 10 ./tester > t16.out 2> t16.err
THRESH=12 NDIVES=12 SEED=99173 nice -n 10 ./tester > t12.out 2> t12.err
echo done > chainA.done
