#!/bin/bash
# rc14 / rc14g audit: pinned sub-instances with split sums (audit code, 2026-10-24).  Single core, nice 10.
# lb packages: with each sub-instance's own LTSB file, reference lwe10b; y40: reference lwe8.  Engines rc13, rc14, rc14g of
# the package, and rc14 / rc14g under LWE11CHECK.  Then peak memory of rc13 / rc14 / rc14g on each package (empty part).
W=<HOME>/c72/audit/c2audit/engine-check/rc14; S=<HOME>/c72/audit/c2audit/engine-check/scripts
F=<HOME>/c72/fleet/pkgs; B=$W/bin
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1
ulimit -v 33554432
cd $W/work || exit 1
for cfg in "y40 4 8 7101" "y40 6 9 7102" "y12-lb2 4 7 7103" "y12-lb2 6 9 7104" "y15-lb 4 8 7105" "y15-lb 5 8 7106"; do
  set -- $cfg; p=$1; L=$2; spl=$3; seed=$4; P=$F/$p; tag=${p}_r14pinL${L}s$spl
  PROBES=20000 PFXLEV=$L PSEED=$seed LTSHFILE=$P/sym.ltsh timeout 120 nice -n 10 $S/lwe8_pfx $P/inst.txt > $tag.raw; grep PREFIX $tag.raw > $tag.pfx; rm -f $tag.raw
  if [ -f $P/sym.ltsb ]; then ENG="--ltsb --eng lwe10b=$B/lwe10b"; else ENG="--eng lwe8=$B/lwe8"; fi
  ENG="$ENG --eng rc13=$B/rc13 --eng rc14=$B/rc14 --eng rc14g=$B/rc14g_$p --eng rc14chk=$B/rc14chk --eng rc14gchk=$B/rc14gchk_$p"
  t0=$(date +%s); timeout 540 nice -n 10 python3 -I $S/difftest_c2.py pin $P $L $W/work/$tag.pfx 8 $seed exact,keep0.9,plant $spl 3 $ENG --tag $tag --work $W/work/$tag --tmo 120 > $W/logs/$tag.log 2>&1
  echo "$tag rc=$? $(tail -1 $W/logs/$tag.log) $(( $(date +%s) - t0 ))s"
done
echo "== peak memory (empty split-2 part; production environment; then the same run under ulimit -v 1048576)"
for p in y40 y12-lb2 y15-lb; do P=$F/$p; ENV="LTSHFILE=$P/sym.ltsh"; [ -f $P/sym.ltsb ] && ENV="$ENV LTSBFILE=$P/sym.ltsb"
  for e in rc13 rc14 rc14g_$p; do
    env $ENV /usr/bin/time -f "%M %e" -o mem.txt nice -n 10 $B/$e $P/inst.txt 2 100000000 99999999 > m1.txt 2>/dev/null
    (ulimit -v 1048576; env $ENV nice -n 10 $B/$e $P/inst.txt 2 100000000 99999999 > m2.txt 2>/dev/null); r2=$?
    echo "$p $e maxrss_KB $(cut -d' ' -f1 mem.txt) wall_s $(cut -d' ' -f2 mem.txt) | under 1 GB ulimit rc=$r2 same=$(cmp -s <(grep -v '^DONE' m1.txt) <(grep -v '^DONE' m2.txt) && echo yes || echo no) | out $(grep -v '^DONE' m1.txt | md5sum | cut -c1-8)"
  done
done
