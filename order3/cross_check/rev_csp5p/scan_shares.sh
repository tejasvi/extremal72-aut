#!/bin/bash
# reviewer scan of the production share files: strict line format, high hex digits, consecutive ids
export TMPDIR=${TMPDIR:-.}
P=${1:?directory holding the per-machine input files}
R=$(cd "$(dirname "$0")" && pwd)
for s in share_hostD share_hostE share_hostC reserve_1 reserve_2 reserve_3; do zcat $P/$s.txt.gz; done | \
  LC_ALL=C awk 'BEGIN{e=0}
  { if ($0 !~ /^[0-9a-f]+ [0-9]+ [0-9]+ [0-9]+ [0-9]+ id=[0-9]+$/) { bf++; if (bf<=5) print "FORMAT", NR, substr($0,1,240) > "/dev/stderr" }
    if (length($1) != 192) { bl++; if (bl<=5) print "LEN", NR, length($1) > "/dev/stderr" }
    t=$1; for (r=0;r<24;r++) if (substr(t,8*r+1,2) != "00") { hb++; if (hb<=5) print "HIGH", NR, r > "/dev/stderr"; break }
    if ($6 != ("id=" e)) { bi++; if (bi<=5) print "ID", NR, $6, e > "/dev/stderr" }
    e++ }
  END { printf "lines=%d badformat=%d badlen=%d highbits=%d badid=%d\n", NR, bf+0, bl+0, hb+0, bi+0 }' > $R/scan_shares.out 2> $R/scan_shares.err
echo "exit=$?" >> $R/scan_shares.out
