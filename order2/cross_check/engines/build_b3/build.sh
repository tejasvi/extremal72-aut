#!/bin/bash
# Build lwe11b, the AVX2 build of lwe11 (same search tree and pruning decisions as lwe8/lwe10/lwe11; see the header of
# lwe11b.c) and record hashes.  Default flags: -O3 -march=x86-64-v3 (AVX2, <CPU>/3, Haswell and later).
#   ./build.sh native              -march=native
set -u
cd "$(dirname "$0")"
export TMPDIR=${TMPDIR:-$(pwd)}
FLAGS="-pipe -O3 -march=x86-64-v3"
[ "${1:-}" = "native" ] && FLAGS="-pipe -O3 -march=native"
gcc $FLAGS -o lwe11b lwe11b.c || exit 1
sha256sum lwe11b.c lwe11b > BUILD.sha256 && echo "flags: $FLAGS" >> BUILD.sha256 && gcc --version | head -1 >> BUILD.sha256 && uname -m >> BUILD.sha256 && cat BUILD.sha256
