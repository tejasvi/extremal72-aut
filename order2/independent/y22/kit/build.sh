#!/bin/bash
# Build the search engine and the brute-force weight tool (gcc, C99). Usage: ./build.sh
set -e
cd "$(dirname "$0")"
mkdir -p tmp
TMPDIR=$PWD/tmp gcc -O3 -march=native -pipe -o engine9 engine.c
TMPDIR=$PWD/tmp gcc -O3 -march=native -pipe -o tests/mincheck tests/mincheck.c
echo built engine9 tests/mincheck
