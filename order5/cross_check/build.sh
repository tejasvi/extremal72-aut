#!/bin/sh
# Build the re-check programs (gen4dump*.c include ../search/common.h).
set -e
cd "$(dirname "$0")"
for p in indep_check indep_check2 indep_check3 indep_check_parts gen4dump gen4dump2; do
  gcc -O3 -march=native -fopenmp -I../search -o "$p" "$p.c" -lm
done
