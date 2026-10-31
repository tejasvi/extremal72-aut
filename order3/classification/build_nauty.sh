#!/bin/bash
# Build the nauty library used by the order-3 programs (both classification programs and the re-checks).
# The computations used nauty 2.9.3 (file nauty2_9_3.tar.gz, sha256
# 9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b), available from
# https://pallini.di.uniroma1.it/ and https://users.cecs.anu.edu.au/~bdm/nauty/ .
# Usage: ./build_nauty.sh nauty2_9_3.tar.gz NAUTYDIR
# Afterwards NAUTYDIR/nauty2_9_3 holds nauty.h, nausparse.h, ... and libnauty64.a; pass that directory
# to the build scripts as NAUTY=.../nauty2_9_3.
set -e
T=$(readlink -f "$1"); mkdir -p "$2"; cd "$2"
tar xzf "$T"; cd nauty2_9_3
./configure > configure.log 2>&1
for f in nauty nautil naugraph schreier naurng nausparse nautinv; do
  gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -c $f.c -o $f.o
done
ar rcs libnauty64.a nauty.o nautil.o naugraph.o schreier.o naurng.o nausparse.o nautinv.o
echo "built $(pwd)/libnauty64.a"
