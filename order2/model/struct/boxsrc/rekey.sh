#!/bin/bash
# rekey.sh CODE CI NTOP CURKEY : (box) key re-selection with the corrected checkability model (keycheck.py, KCSHIFT=1):
# top NTOP orbits -> h0fix key (first 8 words by level) -> LTS probe (PROBES=20000) on the package instance; also the
# current key.  Output lines 'CODE tag est probe key...'.
c=$1; ci=$2; nt=$3; cur=$4; B=<HOME>/struct; R=$B/runs/$c; W=$B/rekey/$c; mkdir -p $W; export TMPDIR=$B/tmp OMP_NUM_THREADS=1
[ -s $R/raw20k.txt ] || PROBES=20000 nice -n 10 $B/runs/frozen3/lwe10 $R/inst.txt > $R/raw20k.txt
KCTOP=$nt <HOME>/venv/bin/python -I $B/src/keycheck.py $ci $R/inst.txt $R/raw20k.txt > $W/kc.txt
pc=$(LTSHFILE=$R/sym.ltsh PROBES=20000 nice -n 10 $B/runs/frozen3/lwe10 $R/inst.txt | tail -n 1 | awk '{print $NF}')
echo "$c current - $pc $cur"
grep '^ORBITWORDS' $W/kc.txt | while read tag i e est n nn w wt words; do
  ws=$(echo $words | cut -d, -f1-8)
  <HOME>/venv/bin/python -I $B/src/mkkey.py $ci $R/inst.txt $R/flag.txt $W/k$i.ltsh h0fix:$ws > $W/k$i.log 2>&1
  kk=$(grep '^KEY' $W/k$i.log | tail -n 1 | cut -d' ' -f2- | tr ' ' ','); kl=$(grep -o 'key levels.*' $W/k$i.log | tail -n 1)
  p=$(LTSHFILE=$W/k$i.ltsh PROBES=20000 nice -n 10 $B/runs/frozen3/lwe10 $R/inst.txt | tail -n 1 | awk '{print $NF}')
  echo "$c orbit$i(n=$nn,wt=$wt) $est $p $kk [$kl]"
  rm -f $W/k$i.ltsh
done
