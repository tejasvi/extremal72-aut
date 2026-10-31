#!/bin/bash
# prefixtime.sh : user CPU of the prefix (levels <= SPL, no part selected) for each packaged code, sequentially
R=<HOME>/struct/runs; export TMPDIR=<HOME>/struct/tmp
for cs in y16:3 y33:3 y27:3 y17:3 y24:3 y18:3 y11:4 y38:3 y2:3 y37:3; do c=${cs%:*}; s=${cs#*:}
  t=$( { LTSHFILE=$R/$c/sym.ltsh nice -n 10 /usr/bin/time -f "%U" $R/frozen3/lwe10 $R/$c/inst.txt $s 1000000000 999999999 > /dev/null; } 2>&1 )
  echo "$c spl$s prefix_user $t"
done
