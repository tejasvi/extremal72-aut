#!/bin/bash
# rekeylb.sh CODE CI NTOP TSTAR : (box) joint key choice for the bit-granular configuration: for the current key and the top
# NTOP orbits of the fixed checkability model (rekey/CODE/kc.txt from rekey.sh), build the greedy basis (partsim2.py at
# TSTAR), the rebased instance, LTSH and LTSB, and probe (PROBES=20000) greedy and greedy+LTSB.
c=$1; ci=$2; nt=$3; ts=$4; B=<HOME>/struct; R=$B/runs/$c; W=$B/rekeylb/$c; mkdir -p $W
export TMPDIR=$B/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1; PY="nice -n 10 $HOME/venv/bin/python -I"
cur=$(grep '^KEY' $R/key.txt | head -n 1 | cut -d' ' -f2- | tr ' ' ',')
{ echo "cur $cur"; grep '^ORBITWORDS' $B/rekey/$c/kc.txt | head -n $nt | awk '{print "o"$2, $NF}'; } | while read tag words; do
  if [ $tag = cur ]; then key=$words; else
    ws=$(echo $words | cut -d, -f1-8)
    $PY $B/src/mkkey.py $ci $R/inst.txt $R/flag.txt $W/$tag.ub.ltsh h0fix:$ws > $W/$tag.mk.log 2>&1
    key=$(grep '^KEY' $W/$tag.mk.log | tail -n 1 | cut -d' ' -f2- | tr ' ' ','); rm -f $W/$tag.ub.ltsh; fi
  k0=${key%%,*}
  GB=$($PY $B/src/partsim2.py $ci $R $k0 $ts 200 $ts | grep GREEDY_BASIS | awk '{print $2}')
  $PY $B/src/rebasis.py $R/inst.txt $W/$tag.txt $k0 $GB > /dev/null
  $PY $B/src/mkkey.py $ci $W/$tag.txt $R/flag.txt $W/$tag.ltsh words:$key > /dev/null 2>&1
  $PY $B/src/mkltsb.py $ci $W/$tag.txt $W/$tag.ltsh $W/$tag.ltsb > /dev/null
  a=$(PROBES=20000 LTSHFILE=$W/$tag.ltsh nice -n 10 $B/src/lwe10b $W/$tag.txt | tail -n 1 | awk '{print $NF}')
  b=$(PROBES=20000 LTSHFILE=$W/$tag.ltsh LTSBFILE=$W/$tag.ltsb nice -n 10 $B/src/lwe10b $W/$tag.txt | tail -n 1 | awk '{print $NF}')
  echo "$c $tag greedy $a greedy+LTSB $b key $key"
  rm -f $W/$tag.txt $W/$tag.txt.meta $W/$tag.txt.pkl $W/$tag.ltsh $W/$tag.ltsb
done
