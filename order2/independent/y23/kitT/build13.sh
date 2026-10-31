#!/bin/bash
set -e
cd "$(dirname "$0")"
mkdir -p tmp
TMPDIR=$PWD/tmp gcc -O3 -march=native -pipe -o engine13 engine13.c
echo built engine13
