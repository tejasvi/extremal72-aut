#!/bin/bash
# Build lwe8 from the frozen source and record hashes.  Default: portable x86-64-v3.  './build.sh native' builds
# with -march=native (~15% faster on <CPU>; results are identical: integer arithmetic only).
cd "$(dirname "$0")"
export TMPDIR=${TMPDIR:-$(pwd)}
ARCH=x86-64-v3; [ "${1:-}" = "native" ] && ARCH=native
gcc -pipe -O3 -march=$ARCH -o lwe8 lwe8.c && sha256sum lwe8.c lwe8 > BUILD.sha256 && echo "march=$ARCH" >> BUILD.sha256 && gcc --version | head -1 >> BUILD.sha256 && uname -m >> BUILD.sha256 && cat BUILD.sha256
