#!/bin/bash
# step1_xreps.sh: orbit representatives of the 36-bit separator (one process, 8 GiB bitmap in-process; needs >= 12 GB
# free). Output xreps18.txt ("0 x" per valid representative), xreps18_log.txt (XREPSFULL / STABHIST lines).
cd "$(dirname "$0")"
export TMPDIR=$PWD/tmp; mkdir -p tmp
avail=$(free -g | awk '/^Mem:/ {print $7}')
[ "$avail" -ge 12 ] || { echo "only $avail GB available"; exit 1; }
[ -e xreps18.txt ] && { echo "xreps18.txt exists"; exit 1; }
( ulimit -v 10485760; exec nice -n 10 ./engine15 sep_A2.eng xrepsfull xaction18.bin xreps18.txt > xreps18_log.txt 2> xreps18_err.txt ) < /dev/null &
echo $! > xreps18.pid
echo "started xrepsfull pid $(cat xreps18.pid) $(date -u)"
