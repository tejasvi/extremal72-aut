#!/bin/bash
# flagkeys.sh NAME CI FLAGFILE NTOP TSTAR [EXTRAKEY] : (box) for a candidate flag: mkinst_c instance, raw probe, fixed-model
# keycheck (top NTOP orbits, plus EXTRAKEY if given) -> for each key: plain LTS probe and greedy basis + LTSB probe.
n=$1; ci=$2; ff=$3; nt=$4; ts=$5; xk=${6:-}; B=<HOME>/struct; W=$B/fk/$n; mkdir -p $W; export TMPDIR=$B/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
PY="nice -n 10 $HOME/venv/bin/python -I"
grep '^FLAG' $ff > $W/flag.txt; $B/src/mkinst_c $B/inst/gen$ci.txt $W/flag.txt $W/inst.txt > /dev/null
PROBES=20000 nice -n 10 $B/runs/frozen3/lwe10 $W/inst.txt > $W/raw20k.txt
echo "$n raw $(tail -n 1 $W/raw20k.txt | awk '{print $NF}')"
KCTOP=$nt $PY $B/src/keycheck.py $ci $W/inst.txt $W/raw20k.txt > $W/kc.txt
{ grep '^ORBITWORDS' $W/kc.txt | awk '{print "o"$2, "h0fix:"$NF}'; [ -n "$xk" ] && echo "x words:$xk"; } | while read tag spec; do
  if [ ${spec%%:*} = h0fix ]; then ws=$(echo ${spec#h0fix:} | cut -d, -f1-8); spec=h0fix:$ws; fi
  $PY $B/src/mkkey.py $ci $W/inst.txt $W/flag.txt $W/$tag.ltsh $spec > $W/$tag.log 2>&1
  key=$(grep '^KEY' $W/$tag.log | tail -n 1 | cut -d' ' -f2- | tr ' ' ','); kl=$(grep -o 'key levels.*' $W/$tag.log | tail -n 1); k0=${key%%,*}
  p=$(PROBES=20000 LTSHFILE=$W/$tag.ltsh nice -n 10 $B/runs/frozen3/lwe10 $W/inst.txt | tail -n 1 | awk '{print $NF}')
  GB=$($PY $B/src/partsim2.py $ci $W $k0 $ts 200 $ts | grep GREEDY_BASIS | awk '{print $2}')
  $PY $B/src/rebasis.py $W/inst.txt $W/$tag.g.txt $k0 $GB > /dev/null
  $PY $B/src/mkkey.py $ci $W/$tag.g.txt $W/flag.txt $W/$tag.g.ltsh words:$key > /dev/null 2>&1
  $PY $B/src/mkltsb.py $ci $W/$tag.g.txt $W/$tag.g.ltsh $W/$tag.g.ltsb > /dev/null
  b=$(PROBES=20000 LTSHFILE=$W/$tag.g.ltsh LTSBFILE=$W/$tag.g.ltsb nice -n 10 $B/src/lwe10b $W/$tag.g.txt | tail -n 1 | awk '{print $NF}')
  echo "$n $tag plain $p greedy+LTSB $b key $key [$kl]"
  rm -f $W/$tag.g.txt $W/$tag.g.txt.meta $W/$tag.g.ltsh $W/$tag.g.ltsb
done
