#!/bin/bash
# level 5 of the E_B classification on hostB: 240 slices
cd "${WORKDIR:-.}" && mkdir -p L5
for s in $(seq 0 239); do
  nohup nice -n 10 ./ebclass 16 5 8 eb/n24.L4.txt L5/s$s $s 240 > L5/log$s.txt 2>&1 < /dev/null &
done
echo launched
