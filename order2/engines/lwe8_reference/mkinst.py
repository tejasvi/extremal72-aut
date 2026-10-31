"""Fast instance builder for the level-wise engine (lwe.c format), plain C2 case (no extra involution).
Same parametrisation as ~/c72/c2par/lwprep.build (bb=None): Gram rows of B in basis w, diagonal equations, gauge
span{D_i} pivots fixed to 0 at the lowest entry indices, reverse-order RREF; free variables ordered by row.
Constraints only for words of weight 8, 10, 12 (weight 14 is vacuous by parity); bad syndromes = patterns of size
< (16-|y|)/2 outside y.  Usage: mkinst.py CI FLAGFILE OUT   (FLAGFILE: line 'FLAG w0 ... w17' from flagbeam)"""
import sys, os, itertools, pickle
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

def build(Ygens, w, m=36, d=16, verbose=True):
    K = m // 2
    ALL = (1 << m) - 1
    W = span_np(Ygens)
    assert len(w) == K and rank(w) == K
    piv = {}
    for k, b in enumerate(w):
        v = b; tr = 1 << k
        for c in sorted(piv, reverse=True):
            if (v >> c) & 1: v ^= piv[c][0]; tr ^= piv[c][1]
        assert v
        piv[v.bit_length() - 1] = (v, tr)
    def coords(x):
        tr = 0
        for c in sorted(piv, reverse=True):
            if (x >> c) & 1: x ^= piv[c][0]; tr ^= piv[c][1]
        assert x == 0
        return tr
    E = [(i, j) for i in range(K) for j in range(i, K)]
    eix = {e: n for n, e in enumerate(E)}
    def ei(i, j): return eix[(i, j) if i <= j else (j, i)]
    NE = len(E)
    def form_mask(ci, cj):
        mm = 0
        for i in range(K):
            if (ci >> i) & 1:
                for j in range(K):
                    if (cj >> j) & 1: mm ^= 1 << ei(i, j)
        return mm
    eqs = []
    cone = coords(ALL)
    for k in range(K):
        mm = (1 << ei(k, k)) ^ form_mask(1 << k, cone)
        if mm: eqs.append((mm, (pc(w[k]) // 2) & 1))
        else: assert (pc(w[k]) // 2) % 2 == 0
    gauge = []
    for p in range(m):
        mm = 0
        for n, (i, j) in enumerate(E):
            if ((w[i] & w[j]) >> p) & 1: mm |= 1 << n
        gauge.append(mm)
    gp = {}
    for g in gauge:
        for b in sorted(gp):
            if (g >> b) & 1: g ^= gp[b]
        if g:
            b = (g & -g).bit_length() - 1
            for b2 in list(gp):
                if (gp[b2] >> b) & 1: gp[b2] ^= g
            gp[b] = g
    grank = len(gp)
    for b in gp: eqs.append((1 << b, 0))
    pv = {}
    for mm, r in eqs:
        for b in sorted(pv, reverse=True):
            if (mm >> b) & 1: mm ^= pv[b][0]; r ^= pv[b][1]
        if not mm:
            assert r == 0, "inconsistent"
            continue
        b = mm.bit_length() - 1
        for b2 in list(pv):
            if (pv[b2][0] >> b) & 1: pv[b2] = (pv[b2][0] ^ mm, pv[b2][1] ^ r)
        pv[b] = (mm, r)
    free = sorted(e for e in range(NE) if e not in pv)
    N = len(free)
    vidx = {e: n for n, e in enumerate(free)}
    level = [E[e][0] for e in free]
    entf = []
    for e in range(NE):
        if e in vidx: entf.append((1 << vidx[e], 0))
        else:
            mm, r = pv[e]; vm = 0
            for b in range(NE):
                if b != e and (mm >> b) & 1:
                    assert b in vidx and b < e
                    vm |= 1 << vidx[b]
            entf.append((vm, r))
    entf_m = np.array([vm for vm, _ in entf], dtype=object); entf_c = [c for _, c in entf]
    def comb_form(emask):
        vm = 0; c = 0
        e = 0
        while emask:
            if emask & 1: vm ^= entf[e][0]; c ^= entf[e][1]
            emask >>= 1; e += 1
        return vm, c
    wt = np.bitwise_count(W)
    cons = []; meta = []
    # weight j is constrained iff some pattern size < (d-j)/2 has the parity of j/2 (other sizes are unreachable)
    jlist = [j for j in range(1, d) if (wt == j).any() and (d - j) // 2 >= 1 + ((j // 2) % 2)]
    for j in jlist:
        for y in W[wt == j].tolist():
            r = (d - j) // 2
            sh = W[(W & np.uint64(y)) == 0].tolist()
            ub = []; red = []
            for u in sh:
                v = u
                for x in red: v = min(v, v ^ x)
                if v: red.append(v); ub.append(u)
            cpos = [i for i in range(m) if not (y >> i) & 1]
            cols = [sum(((ub[t] >> i) & 1) << t for t in range(len(ub))) for i in range(m)]
            bad = set()
            for sz in range(0, r):
                for sub in itertools.combinations(cpos, sz):
                    s = 0
                    for i in sub: s ^= cols[i]
                    bad.add(s)
            cy = coords(y)
            forms = [comb_form(form_mask(cy, coords(u))) for u in ub]
            lv = max([level[v] for (vm, c) in forms for v in range(N) if (vm >> v) & 1] or [0])
            cons.append((lv, j, forms, sorted(bad))); meta.append((y, ub))
    if verbose:
        kt = [sum(1 for v in range(N) if level[v] == t) for t in range(K)]
        print(f"  N = {N} (gauge rank {grank}), k_t = {kt}, constraints {len(cons)}, per level "
              f"{[sum(1 for c in cons if c[0] == t) for t in range(K)]}", flush=True)
    return dict(N=N, level=level, cons=cons, meta=meta, nlev=K, w=w, free=free, E=E, entf=entf, grank=grank)

def export(L, fn):
    N = L['N']; nlev = L['nlev']; level = L['level']
    vstart = [0] * (nlev + 1)
    for t in range(nlev): vstart[t + 1] = vstart[t] + sum(1 for v in range(N) if level[v] == t)
    out = [f"{N} {nlev} {len(L['cons'])}", ' '.join(map(str, vstart))]
    order = sorted(range(len(L['cons'])), key=lambda k: L['cons'][k][0])
    for k in order:
        (lv, wt, forms, bad) = L['cons'][k]
        out.append(f"{lv} {wt} {len(forms)} {len(bad)}")
        for (vm, c) in forms: out.append(f"{vm:x} {c}")
        out.append(' '.join(map(str, bad)))
    open(fn, 'w').write('\n'.join(out) + '\n')
    if 'meta' in L and len(L['meta']) == len(L['cons']):
        mo = []
        for k in order:
            y, ub = L['meta'][k]
            mo.append(' '.join(map(str, [y] + list(ub))))
        open(fn + '.meta', 'w').write('\n'.join(mo) + '\n')

if __name__ == '__main__':
    ci = int(sys.argv[1]); flagfile = sys.argv[2]; out = sys.argv[3]
    codes = load()
    line = [l for l in open(flagfile) if l.startswith('FLAG')][0]
    w = [int(x) for x in line.split()[1:]]
    L = build(codes[ci], w)
    export(L, out)
    pickle.dump(dict(w=L['w'], free=L['free'], entf=L['entf'], N=L['N'], E=L['E']), open(out + '.pkl', 'wb'))
