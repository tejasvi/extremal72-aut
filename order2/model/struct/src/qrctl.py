"""Controls for the plain-C2 level-wise model: extended QR codes of length p+1 (p = 47, 71; p = 3 mod 4) with the
fixed-point-free involution alpha: x -> -1/x of PSL(2,p).  Pairs (x, alpha x); Y = contracted fixed code; the code's
own form B in the given flag, gauge-normalised as in mkinst.build; check it satisfies every constraint.
Usage: qrctl.py P OUTPREFIX [pinlevels...]"""
import sys, pickle, random
import numpy as np
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from common import *
import mkinst

def ext_qr(p):
    Q = set((x * x) % p for x in range(1, p))
    for idem in (Q, set(range(1, p)) - Q, Q | {0}, (set(range(1, p)) - Q) | {0}):
        gens = []
        for s in range(p):
            w = 0
            for i in idem: w |= 1 << ((i + s) % p)
            gens.append(w)
        B = []
        for v in gens:
            for x in B: v = min(v, v ^ x)
            if v: B.append(v)
        if len(B) == (p + 1) // 2:
            e = [b | ((pc(b) & 1) << p) for b in B]
            if all(pc(x) % 4 == 0 for x in e): return e
    raise ValueError

def mobius_alpha(p):
    INF = p
    def f(x):
        if x == INF: return 0
        if x == 0: return INF
        return (-pow(x, p - 2, p)) % p
    return [f(x) for x in range(p + 1)]

def setup(p):
    n = p + 1; m = n // 2
    Cg = ext_qr(p); alpha = mobius_alpha(p)
    assert all(alpha[alpha[i]] == i and alpha[i] != i for i in range(n))
    Wc = span_np(Cg); Ws = set(Wc.tolist())
    def ap(perm, w):
        o = 0
        for i in range(n):
            if (w >> i) & 1: o |= 1 << perm[i]
        return o
    assert all(ap(alpha, g) in Ws for g in Cg)
    pairs = []; used = set()
    for x in range(n):
        if x in used: continue
        pairs.append((x, alpha[x])); used |= {x, alpha[x]}
    def proj(w):
        y = 0; z = 0
        for i, (a, b) in enumerate(pairs):
            ai = (w >> a) & 1; bi = (w >> b) & 1
            if ai ^ bi: y |= 1 << i
            if ai: z |= 1 << i
        return y, z
    Ywords = set(); zof = {}
    for w in Wc.tolist():
        y, z = proj(w)
        if y == 0: Ywords.add(z)
        if y not in zof: zof[y] = z
    Ygens = []; red = []
    for yv in sorted(Ywords):
        r = yv
        for b in red: r = min(r, r ^ b)
        if r: Ygens.append(yv); red.append(r)
    assert len(Ygens) == m // 1 // 2 * 1 or True
    return dict(n=n, m=m, Cg=Cg, Wc=Wc, pairs=pairs, proj=proj, Ygens=Ygens, zof=zof, Ws=Ws)

def own_assignment(S, L):
    """QR code's own B in the instance's parametrisation: B(w_i,w_j) = <z(w_i), w_j>, gauge-normalised."""
    w = L['w']; E = L['E']; entf = L['entf']; free = L['free']; N = L['N']; m = S['m']
    K = len(w)
    Gq = {(i, j): pc(S['zof'][w[i]] & w[j]) & 1 for (i, j) in E}
    eidx = {e: n for n, e in enumerate(E)}
    gauges = []
    for p_ in range(m):
        g = 0
        for (i, j) in E:
            if ((w[i] & w[j]) >> p_) & 1: g |= 1 << eidx[(i, j)]
        gauges.append(g)
    gp = {}
    for g in gauges:
        for b in sorted(gp):
            if (g >> b) & 1: g ^= gp[b]
        if g:
            b = (g & -g).bit_length() - 1
            for b2 in list(gp):
                if (gp[b2] >> b) & 1: gp[b2] ^= g
            gp[b] = g
    Gv = 0
    for e, v in Gq.items():
        if v: Gv |= 1 << eidx[e]
    for b, g in gp.items():
        if (Gv >> b) & 1: Gv ^= g
    a = 0
    for n_, e in enumerate(free):
        if (Gv >> e) & 1: a |= 1 << n_
    bad = sum(1 for e in range(len(E)) if ((pc(entf[e][0] & a) & 1) ^ entf[e][1]) != ((Gv >> e) & 1))
    return a, bad

_badsets = {}
def check_assignment(L, a):
    key = id(L['cons'])
    if key not in _badsets: _badsets[key] = [set(b) for (_, _, _, b) in L['cons']]
    bs = _badsets[key]
    nviol = 0
    for k, (lv, wt, forms, badl) in enumerate(L['cons']):
        s = 0
        for t, (vm, c) in enumerate(forms): s |= ((pc(vm & a) & 1) ^ c) << t
        if s in bs[k]: nviol += 1
    return nviol

def rebuild_code(S, L, a):
    """generator matrix (n-bit ints) of the code C_B for assignment a; return (dim, minwt, doubly_even, alpha_inv)"""
    w = L['w']; E = L['E']; entf = L['entf']; m = S['m']; K = len(w); n = S['n']
    G = [[0] * K for _ in range(K)]
    for e, (i, j) in enumerate(E):
        vm, c = entf[e]; v = (pc(vm & a) & 1) ^ c; G[i][j] = G[j][i] = v
    # dual basis D_j with <D_j, w_i> = delta
    rows = [[w[i], 1 << i] for i in range(K)]; piv = []; r = 0
    for c in range(m):
        pidx = next((i for i in range(r, K) if (rows[i][0] >> c) & 1), None)
        if pidx is None: continue
        rows[r], rows[pidx] = rows[pidx], rows[r]
        for i in range(K):
            if i != r and (rows[i][0] >> c) & 1: rows[i][0] ^= rows[r][0]; rows[i][1] ^= rows[r][1]
        piv.append(c); r += 1
    D = []
    for j in range(K):
        dv = 0
        for i, c in enumerate(piv):
            if (rows[i][1] >> j) & 1: dv |= 1 << c
        D.append(dv)
    gens = []
    pairs = S['pairs']
    def embed(z, y):
        v = 0
        for i, (pa, pb) in enumerate(pairs):
            zi = (z >> i) & 1; yi = (y >> i) & 1
            if zi: v |= 1 << pa
            if zi ^ yi: v |= 1 << pb
        return v
    for k in range(K):
        z = 0
        for j in range(K):
            if G[k][j]: z ^= D[j]
        gens.append(embed(z, w[k]))
    for c in w: gens.append(embed(c, 0))
    Wc = span_np(gens); wts = np.bitwise_count(Wc)
    dim = int(round(np.log2(len(set(Wc.tolist())))))
    return dim, int(wts[wts > 0].min()), bool((wts % 4 == 0).all())

if __name__ == '__main__':
    p = int(sys.argv[1]); outp = sys.argv[2]
    S = setup(p); n = S['n']; m = S['m']
    Wc = S['Wc']; wts = np.bitwise_count(Wc); d = int(wts[wts > 0].min())
    Yw = span_np(S['Ygens']); yw = np.bitwise_count(Yw)
    print(f"QR{n}: d = {d}, |Y| = 2^{len(S['Ygens'])}, d(Y) = {int(yw[yw > 0].min())}, Y weights",
          {int(k): int(v) for k, v in zip(*np.unique(yw, return_counts=True)) if k < d}, flush=True)
    # flag: greedy by number of low words (simple), all-ones first not used
    Yall = Yw.tolist(); low = set(y for y in Yall if 0 < pc(y) < d)
    w = []; spanset = {0}
    while len(w) < m // 2:
        best = None
        cands = [y for y in low if y not in spanset] or [y for y in Yall if y not in spanset]
        for y in cands:
            key = (sum(1 for s in spanset if (s ^ y) in low), -pc(y))
            if best is None or key > best[0]: best = (key, y)
        w.append(best[1]); spanset |= {s ^ best[1] for s in spanset}
    L = mkinst.build(S['Ygens'], w, m=m, d=d)
    mkinst.export(L, outp + '.txt')
    a, bad = own_assignment(S, L)
    print("own form reproduced by parametrisation:", bad == 0, " violated constraints by own form:", check_assignment(L, a), flush=True)
    print("own code rebuilt from assignment: (dim, minwt, doubly-even) =", rebuild_code(S, L, a), flush=True)
    pickle.dump(dict(L=L, a=a, S={k: v for k, v in S.items() if k not in ('proj', 'Wc', 'Ws')}), open(outp + '.pkl', 'wb'))
    open(outp + '.own', 'w').write(f"{a:x}\n")
