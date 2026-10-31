#!/bin/bash
cd <HOME>/lwe11val; same=0; diff=0; miss=0
while read code spl npart p; do
  a=out/lwe8_${code}_${p}.log; b=out/lwe11_${code}_${p}.log
  if [ ! -s $a ] || [ ! -s $b ]; then miss=$((miss+1)); continue; fi
  A=$(grep -E '^LEVEL|^DONE|^SOL' $a | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16); B=$(grep -E '^LEVEL|^DONE|^SOL' $b | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
  if [ "$A" = "$B" ]; then same=$((same+1)); else diff=$((diff+1)); echo "DIFF $code $p"; fi
done < jobs.txt
echo "same $same diff $diff missing $miss (of $(wc -l < jobs.txt))"
