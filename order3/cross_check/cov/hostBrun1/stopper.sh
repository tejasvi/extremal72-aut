#!/bin/bash
# Stop each hostB gtestS slice process (300 slices, start 0) once its progress line shows last >= M.
# The new hostF/hostG processes cover indices >= M (slices of 740). Kills only the exact-argv PID of that slice.
cd "$HOME"/c3class/T24 || exit 1
M=3600000
while true; do
  alive=0
  for s in $(seq 0 299); do
    pid=$(ps -eo pid=,args= | awk -v a="./gtestS R T24/codes.txt $s 300 0" '{p=$1; $1=""; sub(/^ /,""); if ($0==a) print p}')
    [ -z "$pid" ] && continue
    alive=$((alive+1))
    last=$(grep '^progress slice' res$s.txt | tail -1 | awk '{print $7}')
    if [ -n "$last" ] && [ "$last" -ge "$M" ]; then
      kill "$pid" && echo "$(date -u +%FT%TZ) slice $s pid $pid stopped at last=$last" >> stopper.log
    fi
  done
  [ "$alive" -eq 0 ] && { echo "$(date -u +%FT%TZ) no hostB slice processes left; exiting" >> stopper.log; exit 0; }
  sleep 300
done
