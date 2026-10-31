#!/bin/bash
set -e
cd "$(dirname "$0")"
mkdir -p tmp
TMPDIR=$PWD/tmp gcc -O3 -march=native -pipe -o engine15 engine15.c
sha256sum engine15
