"""hoistscan.py INST [LEVEL...] : for the constraints of each level t, the rank of their syndrome forms restricted to the
variables of level t-1 (the parent's row). Rank 0: identical bad-children bitmap for all siblings; rank 1: two bitmaps
(order3-class's hoisting); rank d: 2^d. Also prints the peak-level share by rank."""
import sys, collections
f = open(sys.argv[1]); N, NLEV, NC = map(int, f.readline().split()); vstart = list(map(int, f.readline().split()))
toks = f.read().split(); p = 0
cons = []
for _ in range(NC):
    lv, wt, m, nb = map(int, toks[p:p + 4]); p += 4
    forms = []
    for s in range(m): forms.append(int(toks[p], 16)); p += 2
    p += nb
    cons.append((lv, wt, m, forms))
def rank(vs):
    piv = {}; r = 0
    for v in vs:
        for b in sorted(piv, reverse=True):
            if v >> b & 1: v ^= piv[b]
        if v: piv[v.bit_length() - 1] = v; r += 1
    return r
levels = [int(x) for x in sys.argv[2:]] or range(1, NLEV)
for t in levels:
    lo, hi = vstart[t - 1], vstart[t]
    mask = ((1 << hi) - 1) ^ ((1 << lo) - 1)
    ranks = collections.Counter()
    bywt = collections.defaultdict(collections.Counter)
    for (lv, wt, m, forms) in cons:
        if lv != t: continue
        r = rank([(fm & mask) >> lo for fm in forms]); ranks[r] += 1; bywt[wt][r] += 1
    if ranks:
        print(f"level {t} (kt {vstart[t+1]-vstart[t]}, parent row {hi-lo} vars): constraints {sum(ranks.values())}, rank of parent-row dependence: "
              + ' '.join(f'{r}:{n}' for r, n in sorted(ranks.items())) + ' | by weight: '
              + '; '.join(f'w{w} ' + ' '.join(f'{r}:{n}' for r, n in sorted(c.items())) for w, c in sorted(bywt.items())))
