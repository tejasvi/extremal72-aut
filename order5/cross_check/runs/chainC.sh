#!/bin/bash
cd "${WORKDIR:-.}"
export OMP_NUM_THREADS=32
for rp in '0 13' '0 9' '4 3' '3 31' '3 27' '0 7' '1 30' '3 22'; do set -- $rp
  NPART=32 PART=$2 REP_ONLY=$1 nice -n 10 ./gen4dump > d_r$1_p$2.out 2> d_r$1_p$2.err
done
echo done > chainC.done
