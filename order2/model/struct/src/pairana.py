"""Pairwise projected constraints (2-consistency one level ahead): for constraints c1, c2 at level lv = t+1,
the joint syndrome (s1, s2) = (a1 + M1 v, a2 + M2 v), v = level-lv variables.  The child (level-t assignment) is
dead w.r.t. the pair iff every point of the joint fiber has s1 in Bad1 or s2 in Bad2.  Extra pruning of the pair
beyond its singles = -log2( P(pair alive) / (P(c1 alive) P(c2 alive)) ) estimated exactly by enumerating the
joint fibers over reachable (s1, s2) base points.  Only pairs with joint future rank <= RMAX."""
import sys, math, itertools, random
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *
I = read_inst(sys.argv[1], meta=False); cons = I['cons']; vs = I['vstart']; NLEV = I['NLEV']
RMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3
LEVELS = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else list(range(1, NLEV))
random.seed(5)
def reach_info(c):
    m = c['m']; allrel = relations(c['forms'])
    cst = [sum(c['consts'][i] for i in range(m) if (lam >> i) & 1) & 1 for lam in allrel]
    R = [s for s in range(1 << m) if all((bin(lam & s).count('1') & 1) == k for lam, k in zip(allrel, cst))]
    return R
for lv in LEVELS:
    L = [c for c in cons if c['lv'] == lv]
    if len(L) < 2: continue
    k = vs[lv + 1] - vs[lv]; lo = vs[lv]
    for c in L:
        c['cols'] = [((f >> lo) & ((1 << k) - 1)) for f in c['forms']]   # per syndrome bit: mask over level vars
        # image vectors: for each level variable j, the syndrome column (m bits)
        c['imgcols'] = [sum(((c['cols'][s] >> j) & 1) << s for s in range(c['m'])) for j in range(k)]
        c['bs'] = set(c['bad'])
    tot_extra = 0.0; npairs = 0; nuse = 0
    # sample pairs (all if few)
    pairs = list(itertools.combinations(range(len(L)), 2))
    if len(pairs) > 4000: pairs = random.sample(pairs, 4000)
    scale = (len(L) * (len(L) - 1) / 2) / len(pairs)
    for i, j in pairs:
        c1, c2 = L[i], L[j]
        # joint image basis: v -> (M1 v, M2 v); rank of combined columns
        comb = [(c1['imgcols'][q] | (c2['imgcols'][q] << c1['m'])) for q in range(k)]
        b = Basis(); [b.add(x) for x in comb]
        r12 = len(b)
        if r12 > RMAX: continue
        npairs += 1
        img = [0]
        for x in b.piv.values(): img = img + [y ^ x for y in img]
        # base points: reachable (s1, s2) pairs modulo the joint image -> enumerate a random sample of base points
        R1 = c1.get('R') or reach_info(c1); c1['R'] = R1
        R2 = c2.get('R') or reach_info(c2); c2['R'] = R2
        m1 = c1['m']; M1 = (1 << m1) - 1
        nsamp = 3000; alive_pair = 0; alive1 = 0; alive2 = 0
        for _ in range(nsamp):
            s1 = random.choice(R1); s2 = random.choice(R2); base = s1 | (s2 << m1)
            a1 = a2 = ap = False
            for d in img:
                x = base ^ d; g1 = (x & M1) not in c1['bs']; g2 = (x >> m1) not in c2['bs']
                a1 |= g1; a2 |= g2; ap |= (g1 and g2)
            alive_pair += ap; alive1 += a1; alive2 += a2
        if alive_pair == 0: alive_pair = 0.5
        extra = -math.log2((alive_pair / nsamp) / max(1e-9, (alive1 / nsamp) * (alive2 / nsamp)))
        if extra > 0.01: nuse += 1
        tot_extra += max(0.0, extra)
    print(f"lv={lv:2d} k={k:2d} ncons={len(L):5d} pairs(r12<={RMAX}) {npairs * scale:9.0f} useful {nuse * scale:8.0f} extra prune (sum over pairs, overcounts) {tot_extra * scale:7.2f}", flush=True)
