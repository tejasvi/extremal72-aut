#!/bin/bash
# Build lwe11 rc14g for package y15-lb (rc14 + lane loops generated for this package; gen_check() stops on any other package; with or without LTSBFILE the same search
# tree, pruning decisions and output as rc11/rc13; without LTSBFILE as
# lwe8/lwe10; AVX-512 level filter, see the header of lwe11.c)
# and record hashes.  Default flags: -O3 -march=x86-64-v4 -mavx512vbmi -mgfni -mavx512vpopcntdq (<CPU>/5, <CPU>+).
#   ./build.sh native              -march=native
#   ./build.sh pgo CODEDIR         profile-guided build (about 5% faster): instrumented build, 3 short training parts of
#                                  CODEDIR (split from CODEDIR/PLAN.txt, parts 1..3 of 2000000), rebuild.  The binary then
#                                  depends on the training run; verify it with check_box.sh like any build.
set -u
cd "$(dirname "$0")"
export TMPDIR=${TMPDIR:-$(pwd)}
FLAGS="-pipe -O3 -march=x86-64-v4 -mavx512vbmi -mgfni -mavx512vpopcntdq"
[ "${1:-}" = "native" ] && FLAGS="-pipe -O3 -march=native"
if [ "${1:-}" = "pgo" ]; then
  CODEDIR=$(cd "$2" && pwd); SPL=$(grep '^SPLIT_LEVEL ' $CODEDIR/PLAN.txt | awk '{print $2}')
  PD=$(pwd)/pgo.d; rm -rf $PD; mkdir -p $PD
  gcc $FLAGS -fprofile-generate -fprofile-dir=$PD -o lwe11 lwe11.c || exit 1
  for p in 1 2 3; do LTSHFILE=$CODEDIR/sym.ltsh nice -n 10 ./lwe11 $CODEDIR/inst.txt $SPL 2000000 $p > /dev/null & done; wait
  gcc $FLAGS -fprofile-use -fprofile-dir=$PD -o lwe11 lwe11.c || exit 1
  FLAGS="$FLAGS pgo($CODEDIR)"
else
  gcc $FLAGS -o lwe11 lwe11.c || exit 1
fi
gcc -pipe -O3 -march=x86-64-v3 -o lwe10b lwe10b.c || exit 1   # reference prototype for check_box (LTSB identity)
sha256sum lwe11.c lwe11 lwe10b.c lwe10b > BUILD.sha256 && echo "flags: $FLAGS (lwe10b: -pipe -O3 -march=x86-64-v3)" >> BUILD.sha256 && gcc --version | head -1 >> BUILD.sha256 && uname -m >> BUILD.sha256 && cat BUILD.sha256
