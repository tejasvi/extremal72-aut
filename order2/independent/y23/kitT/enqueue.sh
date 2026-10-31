#!/bin/bash
# enqueue.sh REP NSPLIT: queue items REP.NSPLIT.SPLIT for SPLIT = 0..NSPLIT-1 (skips items already queued/running/done)
cd "$(dirname "$0")"
R=$1; N=$2
[ -f rep_$R.txt ] || { echo "no rep file"; exit 1; }
[ "$N" -ge 1 ] && [ "$N" -le 256 ] || { echo "NSPLIT must be 1..256"; exit 1; }
mkdir -p queue running done out
for k in $(seq 0 $((N - 1))); do
  it=$R.$N.$(printf %03d $k)
  [ -e queue/$it ] || [ -e done/$it ] || ls running/$it.* > /dev/null 2>&1 || : > queue/$it
done
echo "queued: $(ls queue | wc -l)"
