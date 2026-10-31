#!/bin/bash
# mklb.sh NAME CI TSTAR [LBDIR] : bit-granular LTS inputs for package runs/NAME (light: ~1 min, 1 core).
# Writes runs/NAME/lb/: inst.txt(.meta) = the package instance with the key word's constraint rewritten in the greedy
# basis (src/partsim2.py at level TSTAR; src/rebasis.py), sym.ltsh (src/mkkey.py, same key words as the package),
# sym.ltsb (src/mkltsb.py), BUILD.txt (commands, basis, sha256 of everything).
set -eu
n=$1; ci=$2; ts=$3; S=<HOME>/c72/c2opt/struct; R=$S/runs/$n; L=$R/${4:-lb}; mkdir -p $L
export TMPDIR=$S/tmp OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
PY="nice -n 10 <HOME>/c72/venv/bin/python -I"
key=$(grep '^KEY' $R/key.txt | head -n 1 | cut -d' ' -f2- | tr ' ' ',')   # the package's own key (prep_code's key.txt)
k0=${key%%,*}
GB=$($PY $S/src/partsim2.py $ci $R $k0 $ts 200 $ts | grep GREEDY_BASIS | awk '{print $2}')
$PY $S/src/rebasis.py $R/inst.txt $L/inst.txt $k0 $GB > $L/rebasis.log
$PY $S/src/mkkey.py $ci $L/inst.txt $R/flag.txt $L/sym.ltsh words:$key > $L/mkkey.log 2>&1
$PY $S/src/mkltsb.py $ci $L/inst.txt $L/sym.ltsh $L/sym.ltsb > $L/mkltsb.log
{ echo "PACKAGE $n (code index $ci); key words $key; k0 $k0"
  echo "GREEDY_BASIS (bit 0 first, MSB last; partsim2.py at level $ts) $GB"
  echo "BUILD: python -I src/rebasis.py runs/$n/inst.txt runs/$n/lb/inst.txt $k0 <GREEDY_BASIS>"
  echo "       python -I src/mkkey.py $ci runs/$n/lb/inst.txt runs/$n/flag.txt runs/$n/lb/sym.ltsh words:$key"
  echo "       python -I src/mkltsb.py $ci runs/$n/lb/inst.txt runs/$n/lb/sym.ltsh runs/$n/lb/sym.ltsb"
  echo "RUN:   LTSHFILE=lb/sym.ltsh LTSBFILE=lb/sym.ltsb <engine> lb/inst.txt SPL NPART PART  (raw counts = package; LTS counts differ)"
  grep -h 'LTSH:' $L/mkkey.log; cat $L/mkltsb.log
  echo "SHA256:"; (cd $R && sha256sum lb/inst.txt lb/inst.txt.meta lb/sym.ltsh lb/sym.ltsb inst.txt flag.txt)
  echo "TOOLS:"; (cd $S && sha256sum src/partsim2.py src/rebasis.py src/mkkey.py src/mkltsb.py src/ltsblib.py src/partbits_lib.py src/lwe10b.c)
} > $L/BUILD.txt
echo "$n lb done: $(grep -c . $L/BUILD.txt) lines in BUILD.txt; $(cat $L/mkltsb.log)"
