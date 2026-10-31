#!/bin/bash
# valprod.sh NPROC : for every finished lwe8 reference part (logs/ref/<code>_p<part>_lwe8.log with DONE), run bin/lwe11rc5
# on the same part (if not yet done) and compare LEVEL/DONE/SOLUTION lines; summary in logs/val5/PROD_SUMMARY.txt
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
NPROC=$1; mkdir -p logs/val5/prod
for f in logs/ref/*_lwe8.log; do
  grep -q '^DONE' $f || continue; grep -q STOPPED $f && continue
  b=$(basename $f _lwe8.log); code=${b%_p*}; part=${b#*_p}
  read spl npart <<< "$(grep "^$code " logs/ref/PARTS.txt | awk '{print $2, $3}')"
  o=logs/val5/prod/${b}_lwe11
  [ -s $o.log ] && grep -q '^DONE' $o.log && continue
  echo "$code $spl $npart $part $o"
done | xargs -P $NPROC -L 1 sh -c 'src/runpart.sh bin/lwe11rc5 $0 $1 $2 $3 $4'
: > logs/val5/PROD_SUMMARY.txt
for f in logs/ref/*_lwe8.log; do
  b=$(basename $f _lwe8.log); o=logs/val5/prod/${b}_lwe11
  grep -q '^DONE' $f || continue; [ -s $o.log ] || continue
  A=$(grep -E '^LEVEL|^DONE|^SOL' $f | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16); B=$(grep -E '^LEVEL|^DONE|^SOL' $o.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
  n=$(grep '^LEVEL' $f | awk '{s += $8} END {print s}')
  echo "$b lwe8 $A lwe11 $B $([ $A = $B ] && echo IDENTICAL || echo DIFFER) nodes $n user_s lwe8 $(cut -d' ' -f1 logs/ref/${b}_lwe8.time) lwe11 $(cut -d' ' -f1 $o.time)" >> logs/val5/PROD_SUMMARY.txt
done
cat logs/val5/PROD_SUMMARY.txt
