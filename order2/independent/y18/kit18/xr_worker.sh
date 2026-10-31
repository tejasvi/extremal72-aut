#!/bin/bash
# xr_worker.sh K N: orbit representatives for the ranges r = K, K+N, ... < 4096 of [0, 2^36) (2^24 values each), mode
# xrepsmin; skips ranges whose log already has its XREPSMIN line (resumable).
cd "$(dirname "$0")"
K=$1; N=$2
export TMPDIR=$PWD/tmp
for ((r=K; r<4096; r+=N)); do
  f=xr/r_$(printf %04d $r)
  grep -q '^XREPSMIN' $f.log 2>/dev/null && continue
  ./engine15 sep_A2.eng xrepsmin xaction18.bin $(printf %x $((r << 24))) $(printf %x $(((r + 1) << 24))) $f.txt > $f.tmp 2>/dev/null && mv $f.tmp $f.log
done
