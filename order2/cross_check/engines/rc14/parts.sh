#!/bin/bash
# rc14 / rc14g audit: sample parts of the real instances at the production split level 3 (audit code, 2026-10-24).
# Per package: a prefix run gives the level-3 survivors S3; NPART is set for about 2e7 nodes below the split per part and
# part ids are drawn below min(NPART, S3).  Engines: reference (lwe10b + LTSB for lb packages, lwe8 for y40), rc13, rc14,
# rc14g of the package.  Each part is its own job (< 10 min, single core, nice 10).  Stops starting parts after 50 min.
W=<HOME>/c72/audit/c2audit/engine-check/rc14; S=<HOME>/c72/audit/c2audit/engine-check/scripts
F=<HOME>/c72/fleet/pkgs; B=$W/bin
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1
ulimit -v 33554432
cd $W/work || exit 1; T0=$(date +%s)
for cfg in "y40 4.442e15 7201" "y12-lb2 5.467e15 7202" "y15-lb 8.239e15 7203"; do
  set -- $cfg; p=$1; est=$2; seed=$3; P=$F/$p; ENV="LTSHFILE=$P/sym.ltsh"; [ -f $P/sym.ltsb ] && ENV="$ENV LTSBFILE=$P/sym.ltsb"
  t1=$(date +%s); env $ENV timeout 300 nice -n 10 $B/rc14 $P/inst.txt 3 2147483647 2147483646 > pre_$p.txt 2>/dev/null
  read np ids < <(python3 -I - pre_$p.txt $est $seed <<'PY'
import sys, random
l3 = [l.split() for l in open(sys.argv[1]) if l.startswith('LEVEL 3 ')][0]
d = dict(zip(l3[2::2], l3[3::2])); s3 = int(d['nodes']) - int(d['symprune']) - int(d['ltsprune']) - int(d['lhprune'])
np_ = max(1, round(float(sys.argv[2]) / 2e7)); r = random.Random(int(sys.argv[3]))
print(np_, ','.join(str(r.randrange(min(np_, s3))) for _ in range(3)), file=sys.stdout)
print(f'{sys.argv[1]}: level-3 nodes {d["nodes"]} survivors {s3}', file=sys.stderr)
PY
)
  echo "$p prefix run $(( $(date +%s) - t1 ))s, NPART $np, parts $ids"
  if [ -f $P/sym.ltsb ]; then ENG="--ltsb --eng lwe10b=$B/lwe10b"; else ENG="--eng lwe8=$B/lwe8"; fi
  ENG="$ENG --eng rc13=$B/rc13 --eng rc14=$B/rc14 --eng rc14g=$B/rc14g_$p"
  for id in ${ids//,/ }; do
    [ $(( $(date +%s) - T0 )) -gt 3000 ] && { echo "time budget reached, $p part $id not started"; continue; }
    tag=${p}_r14part$id; t1=$(date +%s)
    timeout 580 nice -n 10 python3 -I $S/difftest_c2.py part $P 3 $np $id $ENG --tag $tag --work $W/work/$tag --tmo 560 > $W/logs/$tag.log 2>&1
    echo "  $(grep -h '^OK\|^MISMATCH' $W/logs/$tag.log | cut -c1-200) [$(( $(date +%s) - t1 ))s]"
  done
done
