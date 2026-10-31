"""Projected (partial-syndrome) constraints: for constraint c at level lv and t < lv, the part of the syndrome
determined by levels <= t is u = P s, P = annihilator of Im(L_{>t}) (forms restricted to variables of levels
t+1..lv).  u is projected-bad iff its whole fiber {s : P s = u} lies in Bad.  A projected constraint is checkable
when processing level t (it filters level-t children).  Reports per level t: number of useful projected
constraints and their total heuristic pruning sum -log2(1 - |PB|/|reachable u|)."""
import sys, math, itertools
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *
I = read_inst(sys.argv[1], meta=False); cons = I['cons']; vs = I['vstart']; NLEV = I['NLEV']
DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 3
def lvl_mask(a, b):  # variables of levels a..b inclusive
    lo = vs[a]; hi = vs[b + 1]
    return ((1 << hi) - 1) ^ ((1 << lo) - 1)
gain = [0.0] * (NLEV + 1); cnt = [0] * (NLEV + 1); base = [0.0] * (NLEV + 1)
for c in cons:
    p = pass_prob(c)[0]; base[c['lv']] += -math.log2(p)
from collections import Counter
rk_hist = Counter()
for c in cons:
    lv = c['lv']; m = c['m']; badset = set(c['bad'])
    for t in range(lv - 1, max(-1, lv - 1 - DEPTH), -1):
        fm = lvl_mask(t + 1, lv)
        cols = [f & fm for f in c['forms']]          # future part of each syndrome component
        # image of future: span of column vectors over future variables -> compute as rank of the m x nfut matrix
        # annihilator: lam (m-bit) with sum lam_s cols_s = 0
        rel = relations(cols)                        # basis of annihilator (lam vectors)
        mp = len(rel)
        rk_hist[(lv - t, m - mp)] += 1
        if mp == 0: break
        # projected value u = (lam . s)_lam ; fiber of u = {s : lam_i . s = u_i}
        # count bad fibers: group all s in F2^m by projection
        allrel = relations(c['forms'])
        cst = [sum(c['consts'][i] for i in range(m) if (lam >> i) & 1) & 1 for lam in allrel]
        fib = {}
        for s in range(1 << m):
            if any((bin(lam & s).count('1') & 1) != k for lam, k in zip(allrel, cst)): continue   # unreachable
            u = 0
            for i, lam in enumerate(rel):
                u |= (bin(lam & s).count('1') & 1) << i
            fib.setdefault(u, []).append(s)
        nb = sum(1 for u, ss in fib.items() if all(x in badset for x in ss))
        if nb == 0: break
        nreach = len(fib)
        g = -math.log2(max(1e-12, 1 - nb / nreach))
        gain[t] += g; cnt[t] += 1
for t in range(NLEV):
    print(f"t={t:2d} kt={vs[t+1]-vs[t]:2d} base prune {base[t]:7.2f}  projected: {cnt[t]:5d} cons, extra prune {gain[t]:6.2f}")
print("future-rank histogram (levels ahead, rank of future part):", sorted(rk_hist.items())[:40])
