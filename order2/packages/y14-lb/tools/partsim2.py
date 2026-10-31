"""Vectorised Monte-Carlo of bit-granular LTS tests on component 0 (see partsim.py for the model).
Each transported bit B(g k0, g c_j) is a linear functional of the 171 upper-triangular Gram entries (flag
coordinates), so N random forms are evaluated with one matrix product.  Survival at level t: the current test
(fully determined comparands only) and the bit-granular test (any comparand with a determined, already smaller
MSB-first prefix).  Orders: 'ub' (the instance's syndrome basis) and 'greedy' (MSB first, maximising the number of
non-full comparands at level TSTAR whose determined subspace contains the prefix).
Usage: partsim2.py CI PKGDIR K0 LEVELS NSAMP TSTAR [RAWFILE]"""
import sys, os, pickle, re
import numpy as np
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from partbits_lib import closure, ap

ci = int(sys.argv[1]); pk = sys.argv[2]; k0 = int(sys.argv[3])
levels = [int(x) for x in sys.argv[4].split(',')]; N = int(sys.argv[5]); tstar = int(sys.argv[6])
raw = None
if len(sys.argv) > 7:
    for l in open(sys.argv[7]):
        if 'PROBE estimate' in l: raw = [float(v) for k, v in re.findall(r' (\d+):([\d.e+-]+)', l)]
flag = [int(x) for x in open(f'{pk}/flag.txt').read().split()[1:]]
meta = [list(map(int, l.split())) for l in open(f'{pk}/inst.txt.meta')]
ub = [row[1:] for row in meta if row[0] == k0][0]; m0 = len(ub)
perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
G = closure(perms); idg = G.index(tuple(range(36)))
n = len(flag); words = np.zeros(1 << n, dtype=np.int64); L = np.full(1 << n, -1, dtype=np.int64)
for i, v in enumerate(flag):
    words[1 << i: 1 << (i + 1)] = words[0: 1 << i] ^ v; L[1 << i: 1 << (i + 1)] = i
coord = dict(zip(words.tolist(), range(1 << n))); Lw = dict(zip(words.tolist(), L.tolist()))
Yk = [int(x) for x in words[(words & k0) == 0]]
iu = [(a, b) for a in range(n) for b in range(a, n)]; pos = {p: k for k, p in enumerate(iu)}


def functional(x, y):
    cx = coord[x]; cy = coord[y]; v = np.zeros(len(iu), dtype=np.float32)
    A = [a for a in range(n) if cx >> a & 1]; Bv = [b for b in range(n) if cy >> b & 1]
    for a in A:
        for b in Bv:
            k = pos[(a, b) if a <= b else (b, a)]; v[k] = 1 - v[k]
    return v


def det_lv(g, c):
    u = ap(g, k0); gc = ap(g, c)
    return min(Lw[u], Lw[gc], Lw[u ^ gc])


# greedy basis for level tstar
nonfull = [g for g in G if not (Lw[ap(g, k0)] <= tstar or all(det_lv(g, c) <= tstar for c in ub))]
detset = {g: {c for c in Yk if det_lv(g, c) <= tstar} for g in nonfull}
piv = {}; chosen = []; alive = list(nonfull)
def red(v):
    for b in sorted(piv, reverse=True):
        if v >> b & 1: v ^= piv[b]
    return v
while len(chosen) < m0:
    best = None; bs = -1
    for c in Yk[1:]:
        r = red(c)
        if r == 0: continue
        sc = sum(1 for g in alive if c in detset[g])
        if sc > bs: bs, best, br = sc, c, r
    chosen.append(best); piv[br.bit_length() - 1] = br; alive = [g for g in alive if best in detset[g]]
orders = {'ub': ub, 'greedy': chosen[::-1]}
print('GREEDY_BASIS ' + ','.join(map(str, chosen[::-1])), flush=True)
rng = np.random.default_rng(777)
Msamp = rng.integers(0, 2, size=(len(iu), N)).astype(np.float32)
out = {}
for name, basis in orders.items():
    F = np.zeros((len(G), m0, len(iu)), dtype=np.float32); DL = np.zeros((len(G), m0), dtype=np.int64)
    for gi, g in enumerate(G):
        u = ap(g, k0)
        for j, c in enumerate(basis):
            x = ap(g, c); F[gi, j] = functional(u, x); DL[gi, j] = min(Lw[u], Lw[x], Lw[u ^ x])
    bits = np.zeros((len(G), m0, N), dtype=np.uint8)
    for gi in range(len(G)): bits[gi] = ((F[gi] @ Msamp).astype(np.int64) & 1).astype(np.uint8)
    K0b = bits[idg]
    res = {}
    for t in levels:
        if Lw[k0] > t: res[t] = (1.0, 1.0); continue
        prune_f = np.zeros(N, dtype=bool); prune_p = np.zeros(N, dtype=bool)
        for gi in range(len(G)):
            if gi == idg: continue
            known = DL[gi] <= t; full = bool(known.all())
            und = np.ones(N, dtype=bool); less = np.zeros(N, dtype=bool)
            for j in range(m0 - 1, -1, -1):
                if not known[j]: break
                d = (bits[gi, j] != K0b[j]) & und
                less |= d & (K0b[j] == 1)
                und &= ~d
            if full: prune_f |= less
            prune_p |= less
        res[t] = (1 - prune_f.mean(), 1 - prune_p.mean())
    out[name] = res
    print(f" order {name}: " + '  '.join(f"t{t}: 1/{1 / max(res[t][0], 1e-9):.1f} -> 1/{1 / max(res[t][1], 1e-9):.1f}" for t in levels), flush=True)
if raw:
    # level t nodes are counted after the tests of constraint levels < t (keycheck convention): use survival at t-1
    for name in orders:
        r = out[name]; ef = ep = 0.0
        for t, x in enumerate(raw):
            s = r[t - 1] if (t - 1) in r else (r[max(levels)] if t - 1 > max(levels) else (1.0, 1.0))
            ef += x * s[0]; ep += x * s[1]
        print(f" model total with order {name}: current {ef:.3e}  bit-granular {ep:.3e}  gain {ef / ep:.2f}")
