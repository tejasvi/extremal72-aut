#!/bin/bash
# Build the separate re-check programs of the order-3 pipeline.  Usage: NAUTY=/path/to/nauty2_9_3 ./build.sh
# (NAUTY = directory made by ../classification/build_nauty.sh).  Binaries are written to bin/.
# Some programs include headers of the programs they check: rev_class/src from ../classification/program1/src,
# rev_reclass from ../classification/program2, rev_gtestS from gth/ (copies of the octad-growth headers).
set -e
: "${NAUTY:?set NAUTY to the nauty2_9_3 directory made by ../classification/build_nauty.sh}"
cd "$(dirname "$0")"; mkdir -p bin build
ln -sfn "$NAUTY" build/nauty
P1=../classification/program1/src; P2=../classification/program2/src
CF="-O3 -march=native -DWORDSIZE=64 -DMAXN=0"
L="$NAUTY/libnauty64.a -lz -lm"
for p in autnd autsmall bf cscan ebext lab m24check randinst red72 sampler sextet_gt; do
  gcc $CF -Isrc -I$NAUTY -o bin/$p src/$p.c $L; done
for p in gtestS_xcheck gtestS_prod; do gcc $CF -Igth -I$NAUTY -o bin/$p gth/$p.c $L; done
for p in gtestS_cur gtestS_dumpz gtestS_symchk rankchk test_forb wcount; do
  gcc $CF -Irev_gtestS -Igth -I$NAUTY -o bin/$p rev_gtestS/$p.c $L; done
for p in accinv bdcirc dcirc ebmemb; do gcc $CF -I$P1 -I$NAUTY -o bin/$p rev_class/src/$p.c $L; done
gcc $CF -I../classification/program2 -I$NAUTY -c ../classification/program2/src/ckey.c -o build/ckey.o
for p in cinv ebinv; do gcc $CF -Ibuild -I$NAUTY -I$P2 -o bin/$p rev_reclass/$p.c build/ckey.o $L; done
for p in ebmass gcount; do gcc $CF -o bin/$p rev_reclass/$p.c -lm; done
gcc -O3 -march=native -o bin/csp5p_prov prov/csp5p.c -lm
gcc -O3 -march=native -o bin/csp5p_review rev_csp5p/build/csp5p.c -lm
gcc -O3 -march=native -o bin/csp5p_instr rev_csp5p/instr/csp5p_instr.c -lm
echo "built: $(ls bin | tr '\n' ' ')"
