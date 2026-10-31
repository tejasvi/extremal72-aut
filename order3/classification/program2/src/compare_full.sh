#!/bin/bash
# Compare the second classification (rglue A lines) with the first program's list cls24.txt.
# usage: compare_full.sh RESDIR      (RESDIR/<share>/out/c_XXXX.txt.gz + .txt.eb for all shares)
# Writes RESDIR/cmp/*: sorted extracts and a report (report.txt).
set -u
CLS=${CLS:-$(dirname "$0")/../../class_list/cls24.txt.gz}
R=$(readlink -f "$1"); C=$R/cmp; mkdir -p $C/tmp
export TMPDIR=$C/tmp LC_ALL=C
S="sort -T $C/tmp -S 6G"
rep=$C/report.txt; : > $rep
say() { echo "$*" | tee -a $rep; }
# 1. E_B coverage
cat $R/*/out/c_*.txt.eb > $C/all.eb
say "E_B lines: $(wc -l < $C/all.eb) (expected 45775); distinct ids: $(awk '{print $2}' $C/all.eb | $S -u | wc -l)"
say "E_B id range check (0..45774 each once): $(awk '{print $2}' $C/all.eb | $S -n | awk 'NR-1!=$1{b++} END{print (b+0==0 && NR==45775) ? "OK" : "BAD"}')"
# 2. A lines: per-line consistency own vs cform
zcat $R/*/out/c_*.txt.gz > $C/all.A
say "A lines (distinct per E_B): $(wc -l < $C/all.A)"
say "malformed A lines: $(awk 'NF!=9 || $1!="A" || length($6)!=192' $C/all.A | wc -l)"
say "lines with own aut != cform aut: $(awk '$3!=$7' $C/all.A | wc -l); own selfconj != cform selfconj: $(awk '$4!=$8' $C/all.A | wc -l)"
# 3. own classes vs cform keys (bijection)
awk '{print $2, $6}' $C/all.A | $S -u > $C/pairs.txt
say "distinct (own key, cform key) pairs: $(wc -l < $C/pairs.txt)"
say "distinct own keys (own class count): $(awk '{print $1}' $C/pairs.txt | uniq | wc -l)"
say "distinct cform keys: $(awk '{print $2}' $C/pairs.txt | $S -u | wc -l)"
# 4. (key, aut, A8, sc) multiset vs cls24
awk '{print $6, $7, $5, $8}' $C/all.A | $S -u > $C/mine.kaas
say "distinct (cfkey, aut, A8, sc) records: $(wc -l < $C/mine.kaas); distinct keys among them: $(awk '{print $1}' $C/mine.kaas | uniq | wc -l)"
[ -s $C/cls24.kaas ] || zcat $CLS | awk '{print $1, $2, $3, $4}' | $S > $C/cls24.kaas
say "cls24 records: $(wc -l < $C/cls24.kaas); distinct keys: $(awk '{print $1}' $C/cls24.kaas | uniq | wc -l)"
if cmp -s $C/mine.kaas $C/cls24.kaas; then say "RESULT: (key, aut, A8, selfconj) multisets IDENTICAL"
else
  say "RESULT: DIFFERENCES"
  comm -23 $C/mine.kaas $C/cls24.kaas > $C/only_mine.txt; comm -13 $C/mine.kaas $C/cls24.kaas > $C/only_cls24.txt
  say "  records only in mine: $(wc -l < $C/only_mine.txt); only in cls24: $(wc -l < $C/only_cls24.txt)"
fi
sha256sum $C/mine.kaas $C/cls24.kaas | tee -a $rep
# 5. weighted double count (exact)
python3 -I - $C/all.eb $C/cls24.kaas <<'EOF' | tee -a $rep
import sys
from fractions import Fraction
from collections import Counter
G = 40320 * 3
rhs = Fraction(0)
for line in open(sys.argv[1]):
    f = line.split(); ebaut, ebsc, nphi = int(f[2]), int(f[3]), int(f[5])
    rhs += Fraction((1 if ebsc else 2) * nphi, G * ebaut)
grp = Counter()
for line in open(sys.argv[2]):
    k, aut, a8, sc = line.split(); grp[(int(aut), int(a8), int(sc))] += 1
lhs = sum(Fraction(c * (1 if sc else 2) * a8, 3 * aut) for (aut, a8, sc), c in grp.items())
print(f"double count: LHS (cls24) = {float(lhs):.9f}, RHS (my glue maps) = {float(rhs):.9f}, exact equal: {lhs == rhs}")
print(f"  LHS = {lhs}\n  RHS = {rhs}")
EOF
