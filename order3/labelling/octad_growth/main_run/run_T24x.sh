#!/bin/bash
# Extension of the octad-growth production run (gtestS) to two further machines.
# usage: run_T24x.sh SLICE_FIRST SLICE_LAST   (slices of 740, start index M = 3600000)
cd "${GT_WORKDIR:-.}" && export TMPDIR=${TMPDIR:-$(pwd)/tmp}
M=3600000; NS=740
for s in $(seq $1 $2); do
  if [ -e T24x/res$s.txt ]; then echo "slice $s already has output, skipping"; continue; fi
  nohup nice -n 10 ./gtestS R T24/codes.txt $s $NS $M > T24x/res$s.txt 2>&1 < /dev/null &
done
echo "launched slices $1..$2 of $NS from index $M on $(hostname)"
