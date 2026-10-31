#!/bin/bash
# runlb2.sh JOBFILE NPROC MODE : (box) parts on a package's bit-granular inputs runs/CODE/lb/ (greedy-basis instance + its
# LTSH [+ LTSB]); MODE b = src/lwe10b with LTSBFILE (rc11 configuration), p = frozen3/lwe10 without LTSB (rc9 on the greedy
# basis).  Lines 'CODE SPL NPART PART'; logs samples_lb/CODE_MODE/s<SPL>n<NPART>_p<PART>.log; skips finished parts.
B=<HOME>/struct; export TMPDIR=$B/tmp; M=$3
cat $1 | xargs -P $2 -L 1 sh -c 'c=$0; s=$1; n=$2; p=$3; m='"$M"'; d='"$B"'/samples_lb/${c}${LBDIR:+_$LBDIR}_$m; mkdir -p $d; f=$d/s${s}n${n}_p$p.log
  if [ -s $f ] && grep -q "^DONE" $f; then exit 0; fi
  L='"$B"'/runs/$c/${LBDIR:-lb}
  if [ $m = b ]; then E="LTSHFILE=$L/sym.ltsh LTSBFILE=$L/sym.ltsb"; X='"$B"'/src/lwe10b; else E="LTSHFILE=$L/sym.ltsh"; X='"$B"'/runs/frozen3/lwe10; fi
  env $E nice -n 10 /usr/bin/time -f "user %U wall %e maxrss %M" $X $L/inst.txt $s $n $p > $f.tmp 2>&1 && mv $f.tmp $f'
