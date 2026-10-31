#!/bin/bash
# Build the first classification program and its checks.  Usage: NAUTY=/path/to/nauty2_9_3 ./build.sh
# (NAUTY = directory made by ../build_nauty.sh).  Binaries are written to bin/.
set -e
: "${NAUTY:?set NAUTY to the nauty2_9_3 directory made by ../build_nauty.sh}"
cd "$(dirname "$0")"; mkdir -p bin
CF="-O3 -march=native -DWORDSIZE=64 -DMAXN=0 -Isrc -I$NAUTY"
for p in ebclass ebext frames tisample timiss rsd memb cftest cftest2 clsmiss mkeb rank8; do
  gcc $CF -o bin/$p src/$p.c $NAUTY/libnauty64.a -lm
done
for p in kc fam; do
  gcc $CF -o bin/$p known/$p.c $NAUTY/libnauty64.a -lm
done
echo "built: $(ls bin | tr '\n' ' ')"
