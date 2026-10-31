# For each constraint: level at which each syndrome bit is determined (max level of its variables); report how many
# bits are known before the constraint's own level, and a crude early-pruning estimate from the bad fraction.
import sys
from collections import Counter, defaultdict
tok = open(sys.argv[1]).read().split(); p = 0
def nxt():
    global p; p += 1; return tok[p - 1]
N, NLEV, NC = int(nxt()), int(nxt()), int(nxt()); vs = [int(nxt()) for _ in range(NLEV + 1)]
def lev_of_var(v):
    for l in range(NLEV):
        if vs[l] <= v < vs[l + 1]: return l
    return -1
early = defaultdict(Counter)   # level of constraint -> Counter of (bits known one level early or more)
gap = Counter(); tot = Counter()
for c in range(NC):
    lv, wt, m, nb = int(nxt()), int(nxt()), int(nxt()), int(nxt())
    Ls = []
    for s in range(m):
        hx = nxt(); nxt(); f = int(hx, 16)
        Ls.append(max(lev_of_var(i) for i in range(N) if (f >> i) & 1) if f else -1)
    for _ in range(nb): nxt()
    k = sum(1 for L in Ls if L < lv)        # bits determined before the constraint's level
    early[lv][(wt, m, k)] += 1
    for L in Ls: gap[lv - L] += 1
    tot[lv] += 1
print("bit determination gap (constraint level - bit level): ", dict(sorted(gap.items())))
for lv in sorted(early):
    if lv > 11: break
    print(f"L{lv} ncons {tot[lv]}: (wt, m, bits known early) -> count:", dict(sorted(early[lv].items())))
