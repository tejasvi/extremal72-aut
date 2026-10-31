#!/bin/bash
# jobqc.sh JOBFILE CAP CMD : for each line of JOBFILE run "CMD <line>" in the background while keeping the number
# of my running engine processes (cmdline starting with this directory's src/lwe10) below CAP.
D=<HOME>/c72/c2opt/struct; jf=$1; cap=$2; cmd=$3
while read -r line; do
  [ -z "$line" ] && continue
  while [ "$(pgrep -c -f "^$D/src/lwe10 ")" -ge "$cap" ]; do sleep 3; done
  $cmd $line &
  sleep 0.5
done < "$jf"
wait
echo "jobqc done $jf"
