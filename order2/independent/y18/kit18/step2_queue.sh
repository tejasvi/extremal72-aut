#!/bin/bash
# step2_queue.sh: chunk xreps18.txt into the work queue: first 95% in chunks of 1000 reps (queue/a*), next 4% by 100
# (queue/b*), last 1% by 10 (queue/c*). Refuses to run twice.
set -e
cd "$(dirname "$0")"
[ -d queue ] && { echo "queue exists"; exit 1; }
mkdir -p queue running done out tmp
T=$(wc -l < xreps18.txt); A=$((T * 95 / 100)); B=$((T * 99 / 100))
head -n $A xreps18.txt | split -l 1000 -d -a 6 - queue/a
sed -n "$((A + 1)),${B}p" xreps18.txt | split -l 100 -d -a 6 - queue/b
tail -n +$((B + 1)) xreps18.txt | split -l 10 -d -a 6 - queue/c
echo "reps $T -> chunks $(ls queue | wc -l)"
cat queue/* | wc -l
