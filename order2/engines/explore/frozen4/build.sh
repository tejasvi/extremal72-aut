#!/bin/bash
# Build lwe11 (same search and pruning as frozen/lwe8.c; caching, branch-free inner loops, per-node hoisting; see the header of lwe11.c) and record hashes.
# Default: portable x86-64-v3.  './build.sh native' builds with -march=native (integer arithmetic only).
cd "$(dirname "$0")"
export TMPDIR=${TMPDIR:-$(pwd)}
ARCH=x86-64-v3; [ "${1:-}" = "native" ] && ARCH=native
gcc -pipe -O3 -march=$ARCH -o lwe11 lwe11.c && sha256sum lwe11.c lwe11 > BUILD.sha256 && echo "march=$ARCH" >> BUILD.sha256 && gcc --version | head -1 >> BUILD.sha256 && uname -m >> BUILD.sha256 && cat BUILD.sha256
