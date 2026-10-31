#!/bin/bash
# step1p_collect.sh: check that all 4096 ranges are complete, concatenate them in order into xreps18.txt, and print
# the totals (orbit minima, valid representatives, sum of orbit sizes of the valid ones).
set -e
cd "$(dirname "$0")"
[ -e xreps18.txt ] && { echo "xreps18.txt exists"; exit 1; }
n=$(for r in $(seq 0 4095); do f=xr/r_$(printf %04d $r).log; grep -c '^XREPSMIN' $f 2>/dev/null || echo 0; done | awk '$1==1' | wc -l)
[ "$n" = "4096" ] || { echo "only $n of 4096 ranges complete"; exit 1; }
for r in $(seq 0 4095); do cat xr/r_$(printf %04d $r).txt; done > xreps18.txt
cat xr/r_*.log | awk '$1=="XREPSMIN" {m+=$7; v+=$9; s+=$11} END {printf "orbit minima %d, valid representatives %d, sum of orbit sizes of the valid %.0f\n", m, v, s}'
wc -l < xreps18.txt
sha256sum xreps18.txt
cat xr/r_*.log | awk '$1=="STABHIST" {for (i=2; i<=NF; i++) {split($i, a, ":"); h[a[1]]+=a[2]}} END {printf "STABHIST"; n=asorti(h, k, "@ind_num_asc"); for (i=1; i<=n; i++) printf " %s:%d", k[i], h[k[i]]; printf "\n"}'
