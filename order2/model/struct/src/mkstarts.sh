#!/bin/bash
# mkstarts.sh CI : invariant-start candidates (ginvstart, dim <= 7), top-2 by pruning L per dim 2..7, MAXL
# continuation (flagbeam4, beam 1000) -> inst/starts/s{CI}_{K}.flag ; prints scan-job lines for scan_one2.sh
ci=$1; D=<HOME>/c72/c2opt/struct; export TMPDIR=$D/tmp
[ -s $D/logs/starts/y$ci.cands7 ] || nice -n 10 <HOME>/c72/venv/bin/python -I $D/src/ginvstart.py $ci 7 > $D/logs/starts/y$ci.cands7
awk '{d=$2; L=substr($4,3)+0; print NR, d, L}' $D/logs/starts/y$ci.cands7 | sort -k2,2n -k3,3gr | awk '$2>=2 {c[$2]++; if (c[$2]<=2) print $1}' | while read K; do
  f=$D/inst/starts/s${ci}_$K.flag
  if [ ! -s $f ]; then
    PRE=$(sed -n "${K}p" $D/logs/starts/y$ci.cands7 | awk '{print $NF}')
    MAXL=1 nice -n 10 $D/src/flagbeam4 $D/inst/data/gen_$ci.txt $D/inst/data/low_$ci.txt 1000 "$PRE" 2> /dev/null | grep "FLAG\|PEAK" > $f
  fi
  echo "$ci st${ci}_$K $f 50000"
done
