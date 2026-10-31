#!/bin/bash
# jobq2.sh JOBFILE CAP : run each line of JOBFILE (args for runpart.sh) in the background, keeping the number of
# my running engine processes (cmdline starting with this directory's src/lwe10, any batch) below CAP.
# Lines whose .time file is non-empty are skipped (resumable).
D=<HOME>/c72/c2opt/struct; cap=$2
while read -r a b c d e f; do
  [ -z "$a" ] && continue
  [ -s "$f.time" ] && continue
  while [ "$(pgrep -c -f "^$D/src/lwe10 ")" -ge "$cap" ]; do sleep 5; done
  $D/src/runpart.sh $a $b $c $d $e $f &
  sleep 1
done < "$1"
wait
echo "jobq done $1"
