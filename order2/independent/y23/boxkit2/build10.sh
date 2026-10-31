#!/bin/bash
set -e
cd "$(dirname "$0")"
mkdir -p tmp
TMPDIR=$PWD/tmp gcc -O3 -march=native -pipe -o engine10 engine10.c
echo built engine10
