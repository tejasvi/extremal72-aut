#!/bin/bash
# idcheck_lb.sh CODE SPL NPART PART : (box) identity checks of an rc11 package on a chosen part (check_box's part 17 of 200000
# holds ~1e9-1e10 nodes for the core codes): (1) without LTSB: explore frozen/lwe8 vs frozen3/lwe10 (LEVEL/DONE/SOLUTION);
# (2) with LTSBFILE=sym.ltsb: struct lwe10b vs alg's frozen_b5 lwe11b (rc11 AVX2 build) (LEVEL/DONE/SOLUTION/LBPRUNE).
c=$1; s=$2; n=$3; p=$4; B=<HOME>/struct; R=$B/runs; D=$R/$c; export TMPDIR=$B/tmp
norm() { grep -E "$1" | sed 's/time [0-9]*s//'; }
A=$(LTSHFILE=$D/sym.ltsh nice -n 10 $R/frozen/lwe8 $D/inst.txt $s $n $p | norm '^LEVEL|^SOLUTION|^DONE' | tee $B/idlb_${c}_lwe8.txt | sha256sum)
Bv=$(LTSHFILE=$D/sym.ltsh nice -n 10 $R/frozen3/lwe10 $D/inst.txt $s $n $p | norm '^LEVEL|^SOLUTION|^DONE' | sha256sum)
[ "$A" = "$Bv" ] && r1="IDENTICAL" || r1="DIFFER"
C=$(LTSHFILE=$D/sym.ltsh LTSBFILE=$D/sym.ltsb nice -n 10 $B/frozen_b5/lwe10b $D/inst.txt $s $n $p | norm '^LEVEL|^SOLUTION|^DONE|^LBPRUNE' | tee $B/idlb_${c}_lwe10b.txt | sha256sum)
Dv=$(LTSHFILE=$D/sym.ltsh LTSBFILE=$D/sym.ltsb nice -n 10 $B/frozen_b5/lwe11b $D/inst.txt $s $n $p | norm '^LEVEL|^SOLUTION|^DONE|^LBPRUNE' | sha256sum)
[ "$C" = "$Dv" ] && r2="IDENTICAL" || r2="DIFFER"
nodes=$(awk '/^LEVEL/ {s += $8} END {print s}' $B/idlb_${c}_lwe8.txt); lb=$(grep -o 'LBPRUNE.*' $B/idlb_${c}_lwe10b.txt | awk '{s=0; for (i=2;i<=NF;i++) {split($i,a,":"); s+=a[2]} print s}')
echo "$c part $p of $n at split $s ($nodes nodes): LWE8/LWE10 without LTSB $r1; LWE10B/LWE11B(rc11 b5) with LTSBFILE $r2 (LBPRUNE total $lb)"
