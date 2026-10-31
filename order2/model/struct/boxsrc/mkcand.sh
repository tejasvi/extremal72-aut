#!/bin/bash
# mkcand.sh CI TAG FLAGFILE KEYSPEC : (box) candidate run dir <HOME>/struct/runs/c{CI}_{TAG}: inst.txt (mkinst_c), sym.ltsh
# (mkkey.py KEYSPEC, H0 fixed), key line, prefix survivors at levels 2..4 (stop when the prefix gets expensive)
ci=$1; tag=$2; flag=$3; spec=$4; B=<HOME>/struct; export TMPDIR=$B/tmp; d=$B/runs/c${ci}_$tag; mkdir -p $d
grep '^FLAG' $flag > $d/flag.txt
[ -s $d/inst.txt ] || $B/src/mkinst_c $B/inst/gen$ci.txt $d/flag.txt $d/inst.txt > /dev/null
[ -s $d/sym.ltsh ] || <HOME>/venv/bin/python -I $B/src/mkkey.py $ci $d/inst.txt $d/flag.txt $d/sym.ltsh $spec > $d/mkkey.log 2>&1
grep -h "stabiliser\|LTSH\|^KEY" $d/mkkey.log | tr '\n' ' '; echo
for s in 2 3 4; do
  r=$( { LTSHFILE=$d/sym.ltsh timeout 120 /usr/bin/time -f "%U" $B/runs/frozen3/lwe10 $d/inst.txt $s 1000000000 999999999 | grep "^LEVEL $s " | awk '{print $8-$16}'; } 2>&1 | tr '\n' ' ')
  echo "c${ci}_$tag spl$s survivors,prefix_s: $r"
done
