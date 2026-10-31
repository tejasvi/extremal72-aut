#!/bin/bash
# length-24 R2 frame search over the 45775 E_B classes on hostB: 288 slices
cd "${WORKDIR:-.}" && mkdir -p F24
for s in $(seq 0 287); do
  nohup nice -n 10 ./frames 24 8 eb/n24.L5.txt F24/out$s.txt $s 288 > F24/log$s.txt 2>&1 < /dev/null &
done
echo launched
