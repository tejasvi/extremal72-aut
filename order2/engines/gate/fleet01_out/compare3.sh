#!/bin/bash
cd <HOME>/lwe11val; read code spl npart parts < PARTS_y29.txt
for e in rc7 l11b rc9; do same=0; diff=0; miss=0
  for p in $parts; do a=out/lwe8_${code}_${p}.log; b=out/${e}_${code}_${p}.log
    if [ ! -s $a ] || [ ! -s $b ]; then miss=$((miss+1)); continue; fi
    A=$(grep -E '^LEVEL|^DONE|^SOL' $a | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16); B=$(grep -E '^LEVEL|^DONE|^SOL' $b | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
    if [ "$A" = "$B" ]; then same=$((same+1)); else diff=$((diff+1)); echo "DIFF $e $code $p"; fi
  done
  echo "$e vs lwe8 (y29): same $same diff $diff missing $miss (of 20); SOL lines in $e: $(cat out/${e}_y29_*.log 2>/dev/null | grep -c '^SOL')"
done
