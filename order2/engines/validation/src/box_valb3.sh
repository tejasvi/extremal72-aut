#!/bin/bash
# box_valb.sh : lwe11b validation on the box (<CPU>). Builds forced-path variants, then runs every job (xargs -P 60).
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/valb3/std logs/valb3/check logs/valb3/force logs/valb3/prod logs/valb3/paired
F="-pipe -O3 -march=x86-64-v3"; S=src/lwe11b3.c
gcc $F -DVECCAP=0 -o bin/b3_t1novec $S; gcc $F -DTRCAP=0 -o bin/b3_t2rest $S; gcc $F -DOPT_ARENA=0 -o bin/b3_t3noarena $S
gcc $F -DDCAP=0 -o bin/b3_t4nodirect $S; gcc $F -DDCAP=1048576 -o bin/b3_t5alldirect $S
sha256sum bin/lwe11b3 bin/b3_t* bin/lwe10_g14 src/lwe11b3.c > logs/valb3/BINARIES.sha256
{
for c in y8 y4 y5 y5b y22 y23 y1 y1b y29 y28 y17 y17b y35 y18; do echo "std $c"; done
for j in "y29 2 200000000 782" "y28 3 40000000 1795" "y17 3 20000000 5407" "y8 3 200000 17" "y5b 3 4000000 17" "y23 3 4000000 17" "y1b 3 8000000 17" "y4 2 4000000 17" "y35 3 40000000 17" "y18 3 80000000 17" "y22 3 4000000 17" "y17b 3 20000000 17" "y5 3 4000000 17" "y1 3 8000000 17" "y18 3 2000000 17"; do echo "check $j"; done
for t in t1novec t2rest t3noarena t4nodirect t5alldirect; do for j in "y29 2 200000000 782" "y28 3 40000000 1795" "y17 3 20000000 5407"; do echo "force $t $j"; done; done
for j in "y29 3 4000 1461" "y29 3 4000 1599" "y29 3 4000 2170" "y28 3 8000 1668" "y28 3 8000 2465" "y28 3 8000 5043" "y17 3 8000 427" "y17 3 8000 5407"; do echo "prod $j"; done
} > logs/valb3/jobs.txt
cat logs/valb3/jobs.txt | xargs -P 60 -L 1 src/box_valb3job.sh
echo VALB3_DONE
