#!/bin/bash
# Build the second classification program.  Usage: NAUTY=/path/to/nauty2_9_3 ./build.sh
# (NAUTY = directory made by ../build_nauty.sh).  Binaries are written to bin/.
# src/mycanon.h includes "../f4code.h" (this directory) and "nauty/nauty.h"; src/ckey.c includes
# "c3c/cform.h", a copy of the first program's canonical form used only to compare the two lists.
set -e
: "${NAUTY:?set NAUTY to the nauty2_9_3 directory made by ../build_nauty.sh}"
cd "$(dirname "$0")"; mkdir -p bin build
ln -sfn "$NAUTY" build/nauty
CF="-O3 -march=native -DWORDSIZE=64 -DMAXN=0 -Ibuild -I$NAUTY -I. -Isrc"
gcc $CF -c src/ckey.c -o build/ckey.o
gcc $CF -o bin/ebcls2 src/ebcls2.c $NAUTY/libnauty64.a -lm
gcc $CF -o bin/rglue src/rglue.c build/ckey.o $NAUTY/libnauty64.a -lm
gcc $CF -o bin/ebkey src/ebkey.c build/ckey.o $NAUTY/libnauty64.a -lm
echo "built: $(ls bin | tr '\n' ' ')"
