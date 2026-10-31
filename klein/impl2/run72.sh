#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/.." && pwd)"; export KLEIN
# Run the engine on all length-72 instances (12 parallel processes, nice 10).
cd $KLEIN/impl2
ls inst/i72_*.txt | sed 's#inst/##; s#\.txt##' | \
  xargs -P 12 -I{} sh -c 'nice -n 10 ./search inst/{}.txt > logs/run_{}.out 2> logs/run_{}.err'
echo ALLDONE > logs/run72.done
