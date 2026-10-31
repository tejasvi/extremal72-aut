#!/bin/bash
set -e
cd "$(dirname "$0")"
mkdir -p tmp
TMPDIR=$PWD/tmp gcc -O3 -march=native -pipe -o engine9 engine.c
echo built engine9
