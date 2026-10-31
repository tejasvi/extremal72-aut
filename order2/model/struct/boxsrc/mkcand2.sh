#!/bin/bash
# mkcand2.sh CI TAG : (box) for flag var/TAG.flag (scanned as scan/y{CI}_{SCANTAG}_key.txt) build two candidate dirs:
# runs/c{CI}_{TAG}_e (early:8 key) and runs/c{CI}_{TAG}_o (best-orbit key, H0-fixed); print key levels + SPL3 survivors
ci=$1; tag=$2; B=<HOME>/struct; export TMPDIR=$B/tmp; ff=$B/var/$tag.flag
st=$(echo $tag | sed "s/^u${ci}_/u/"); sk=$B/scan/y${ci}_${st}_key.txt
bw=$(grep BESTWORDS $sk | awk '{print $2}' | cut -d, -f1-8)
for v in e o; do d=$B/runs/c${ci}_${tag}_$v; mkdir -p $d; grep '^FLAG' $ff > $d/flag.txt
  [ -s $d/inst.txt ] || $B/src/mkinst_c $B/inst/gen$ci.txt $d/flag.txt $d/inst.txt > /dev/null
  if [ $v = e ]; then spec=early:8; else spec=h0fix:$bw; fi
  [ -s $d/sym.ltsh ] || <HOME>/venv/bin/python -I $B/src/mkkey.py $ci $d/inst.txt $d/flag.txt $d/sym.ltsh $spec > $d/mkkey.log 2>&1
  sv=$(LTSHFILE=$d/sym.ltsh timeout 200 $B/runs/frozen3/lwe10 $d/inst.txt 3 1000000000 999999999 | grep "^LEVEL 3 " | awk '{print $8-$16}')
  echo "c${ci}_${tag}_$v $(grep -h 'key levels' $d/mkkey.log | tail -1 | sed 's/.*key levels/levels/') spl3_survivors $sv"
done
