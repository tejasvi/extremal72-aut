#!/bin/bash
cd "${WORKDIR:-.}"
while [ ! -f chainC.done ]; do sleep 20; done
export OMP_NUM_THREADS=32
SMP1=1 SMP2=1 SMP3=1 NPART=32 PART=1 REP_ONLY=6 nice -n 10 ./gen4dump2 > f_r6_p1.out 2> f_r6_p1.err
for rp in '2 5' '5 13' '1 25' '6 20'; do set -- $rp
  NPART=32 PART=$2 REP_ONLY=$1 nice -n 10 ./gen4dump2 > s_r$1_p$2.out 2> s_r$1_p$2.err
done
echo done > chainD.done
