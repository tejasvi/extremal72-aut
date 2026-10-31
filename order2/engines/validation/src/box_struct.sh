#!/bin/bash
# box_struct.sh : lwe11b on every struct sample part (same split/NPART/part as the package's lwe10 samples) and one
# LWE11CHECK part per package.  Summaries: logs/struct/SAMPLES.txt (identity + times), logs/struct/CHECKS.txt
cd <HOME>/alg; export TMPDIR=<HOME>/alg/tmp; mkdir -p logs/struct
{ for d in struct/y*/; do d=$(basename $d); [ -f struct/$d/PLAN.txt ] || continue
    for f in struct/$d/samples/*.log; do b=$(basename $f .log); echo "sample $d $b"; done
    first=$(ls struct/$d/samples/*.log | head -1); echo "check $d $(basename $first .log)"
  done; } > logs/struct/jobs.txt
cat logs/struct/jobs.txt | xargs -P 50 -L 1 src/box_structjob.sh
echo STRUCT_DONE
