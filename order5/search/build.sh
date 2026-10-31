#!/bin/sh
# Build the search program and its tools with GCC and OpenMP (binaries are written next to the sources).
set -e
cd "$(dirname "$0")"
for p in gen4 gen4d5 gen2h tester planted2 ngcount selftest unit; do
  gcc -O3 -march=native -fopenmp -o "$p" "$p.c" -lm
done
for p in gen gen2 gen2p gen3 gen3h gen3p planted; do
  gcc -O3 -march=native -fopenmp -I. -o "development/$p" "development/$p.c" -lm
done
