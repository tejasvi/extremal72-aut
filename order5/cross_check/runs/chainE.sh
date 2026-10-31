#!/bin/bash
cd "${WORKDIR:-.}"
while [ ! -f chainD.done ]; do sleep 20; done
export OMP_NUM_THREADS=32
( time nice -n 10 ./indep_check3 < f_r6_p1.out ) > chk_f_r6_p1.txt 2>&1
for f in s_r2_p5 s_r5_p13 s_r1_p25 s_r6_p20 d_r3_p22; do
  ( time nice -n 10 ./indep_check3 < $f.out ) > chk_$f.txt 2>&1
done
echo done > chainE.done
