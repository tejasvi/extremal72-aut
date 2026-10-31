#!/bin/bash
# step1p_xreps.sh N: orbit representatives in parallel (xrepsmin over 4096 ranges, N detached workers, nice 10,
# ulimit -v 1 GiB). Resumable. When all 4096 logs are complete, run ./step1p_collect.sh.
cd "$(dirname "$0")"
N=$1
[ "$N" -ge 1 ] 2>/dev/null && [ "$N" -le 380 ] || { echo "N must be 1..380"; exit 1; }   # guard against process explosions
mkdir -p xr tmp
for ((k=0; k<N; k++)); do
  ( ulimit -v 1048576; exec nice -n 10 ./xr_worker.sh $k $N ) < /dev/null > /dev/null 2>&1 &
done
echo "started $N xrepsmin workers $(date -u)"
