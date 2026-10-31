#!/bin/bash
# idcheck.sh CODE SPL NPART PART : (box) the LWE8/LWE10 identity step of explore's frozen3/check_box.sh on a chosen part
# (check_box.sh fixes part 17 of 200000, which holds ~1e10 nodes for the core codes); same normalisation of LEVEL lines.
c=$1; s=$2; n=$3; p=$4; B=<HOME>/struct; R=$B/runs; export TMPDIR=$B/tmp
A=$(LTSHFILE=$R/$c/sym.ltsh nice -n 10 $R/frozen/lwe8 $R/$c/inst.txt $s $n $p | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | tee $B/idcheck_${c}_lwe8.txt | sha256sum)
Bv=$(LTSHFILE=$R/$c/sym.ltsh nice -n 10 $R/frozen3/lwe10 $R/$c/inst.txt $s $n $p | grep -E '^LEVEL|^SOLUTION|^DONE' | sed 's/time [0-9]*s//' | tee $B/idcheck_${c}_lwe10.txt | sha256sum)
nodes=$(awk '/^LEVEL/ {s += $8} END {print s}' $B/idcheck_${c}_lwe10.txt)
[ "$A" = "$Bv" ] && echo "$c LWE8/LWE10 IDENTICAL (part $p of $n at split $s; $nodes nodes)" || echo "$c LWE8/LWE10 DIFFER (part $p of $n at split $s)"
