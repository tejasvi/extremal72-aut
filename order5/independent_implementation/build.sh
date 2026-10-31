#!/bin/sh
# Build the separate implementation (the compile command used for its runs).
set -e
cd "$(dirname "$0")/src"
for f in *.c; do
  gcc -O3 -march=native -fopenmp -Wall -Wno-unused-function -o "${f%.c}" "$f"
done
