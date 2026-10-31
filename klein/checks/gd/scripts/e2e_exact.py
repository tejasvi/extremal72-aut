"""Exact verification of all class forms of an instance + independent good-set recomputation for sampled words.
Forms: an affine map F2^nW -> F2 is determined by its values at 0 and the unit vectors; for each of these nW+1
points w we build z0 from B(w) with our own dual basis and compare <z0(y), u_t> with the instance form.
Good sets: for sampled words, for every class g build x_g on comp(y) with syndrome g and compute the true coset
minimum weight min_{c in Y} |(x_g + c) & comp| (numpy over all 2^18 words of Y); good <=> min >= (16-|y|)/2."""
import sys, os, pickle, random
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np
sys.path.insert(0, HERE + '/../../../model')
from v4sat import setup, group_elements, fpf_involution_classes
from autinv import load
M = 36; K = 18
def pc(x): return bin(x).count('1')
def rank_list(vs):
    piv = {}
    for v in vs:
        while v:
            h = v.bit_length() - 1
            if h in piv: v ^= piv[h]
            else: piv[h] = v; break
    return len(piv)
def parse_inst(fn):
    L = open(fn).read().split('\n'); nW, nw = map(int, L[0].split()); p = 1; words = []
    for _ in range(nw):
        wt, d, ng = map(int, L[p].split()); p += 1; forms = []
        for t in range(d):
            m, c = L[p].split(); p += 1; forms.append((int(m, 16), int(c)))
        good = set(map(int, L[p].split())) if ng else set(); p += 1
        words.append((wt, d, forms, good))
    return nW, words
def main(ci, ri, nsample, seed):
    codes = load(); res = pickle.load(open(HERE + '/../../../model/invs.pkl', 'rb'))
    G = group_elements(res[ci]['perms']); reps, _ = fpf_involution_classes(G); bb = list(reps[ri])
    S = setup(codes[ci], bb, verbose=False)
    nW, words = parse_inst(f'{HERE}/../../../gd_runs/inst/v4_{ci}_{ri}.txt')
    assert nW == S['nW']
    basis = S['basis']; Wv = S['W']; part = S['part']; E = S['ei']
    recs = sorted(S['recs'], key=lambda r: pc(r[0]))
    assert len(recs) == len(words)
    # shortened-code bases
    U = []
    for q, (y, sbc, bits, bad) in enumerate(recs):
        us = []
        for c in sbc:
            u = 0
            for i in range(K):
                if (c >> i) & 1: u ^= basis[i]
            us.append(u)
        assert all(u & y == 0 for u in us)
        # independent dimension of {u in Y : u & y = 0} = 18 - rank(Y|supp y)
        pos = [i for i in range(M) if (y >> i) & 1]
        restr = [sum(((b >> p_) & 1) << k for k, p_ in enumerate(pos)) for b in basis]
        dim_short = K - rank_list(restr)
        assert len(us) == dim_short == rank_list(us) == words[q][1], (q, len(us), dim_short)
        U.append(us)
    # own dual basis
    rows = [[basis[i], 1 << i] for i in range(K)]; pivc = []; r = 0
    for c in range(M):
        p_ = next((i for i in range(r, K) if (rows[i][0] >> c) & 1), None)
        if p_ is None: continue
        rows[r], rows[p_] = rows[p_], rows[r]
        for i in range(K):
            if i != r and (rows[i][0] >> c) & 1: rows[i][0] ^= rows[r][0]; rows[i][1] ^= rows[r][1]
        pivc.append(c); r += 1
    D = []
    for j in range(K):
        dv = 0
        for i, c in enumerate(pivc):
            if (rows[i][1] >> j) & 1: dv |= 1 << c
        D.append(dv)
    # coefficient vectors of the y's (own elimination)
    piv = {}
    for k, b in enumerate(basis):
        v, c = b, 1 << k
        while v:
            h = v.bit_length() - 1
            if h in piv: v ^= piv[h][0]; c ^= piv[h][1]
            else: piv[h] = (v, c); break
    def coef(x):
        c = 0
        while x:
            h = x.bit_length() - 1; pv, pcf = piv[h]; x ^= pv; c ^= pcf
        return c
    cys = [coef(rec[0]) for rec in recs]
    pts = [0] + [1 << t for t in range(nW)]
    nbad = 0
    for w in pts:
        vec = part
        for t in range(nW):
            if (w >> t) & 1: vec ^= Wv[t]
        z0b = []
        for k in range(K):
            z = 0
            for j in range(K):
                if (vec >> E(k, j)) & 1: z ^= D[j]
            z0b.append(z)
        for q in range(len(words)):
            z = 0; cy = cys[q]
            for k in range(K):
                if (cy >> k) & 1: z ^= z0b[k]
            forms = words[q][2]
            for t, u in enumerate(U[q]):
                true_bit = pc(z & u) & 1
                m, c = forms[t]
                inst_bit = (pc(m & w) & 1) ^ c
                if true_bit != inst_bit:
                    nbad += 1
    print(f'{ci}_{ri}: forms checked at {len(pts)} points x {sum(len(u) for u in U)} forms: mismatches {nbad}', flush=True)
    # good sets for sampled words
    Ylist = [0]
    for b in basis: Ylist = Ylist + [x ^ b for x in Ylist]
    YA = np.array(Ylist, dtype=np.uint64)
    rng = random.Random(seed)
    byw = {}
    for q, rec in enumerate(recs): byw.setdefault(pc(rec[0]), []).append(q)
    sample = []
    for wt in sorted(byw): sample += rng.sample(byw[wt], min(nsample, len(byw[wt])))
    gmis = 0; ncls = 0
    for q in sample:
        y = recs[q][0]; comp = ((1 << M) - 1) & ~y; rr = (16 - pc(y)) // 2
        us = U[q]; d = len(us)
        # solve for x_g: build x_t with <x_t, u_s> = delta_ts, supported on comp
        cpos = [i for i in range(M) if (comp >> i) & 1]
        Mrows = [[sum(((u >> p_) & 1) << k for k, p_ in enumerate(cpos)), 1 << t] for t, u in enumerate(us)]
        pv2 = []; r2 = 0
        for c in range(len(cpos)):
            p_ = next((i for i in range(r2, d) if (Mrows[i][0] >> c) & 1), None)
            if p_ is None: continue
            Mrows[r2], Mrows[p_] = Mrows[p_], Mrows[r2]
            for i in range(d):
                if i != r2 and (Mrows[i][0] >> c) & 1: Mrows[i][0] ^= Mrows[r2][0]; Mrows[i][1] ^= Mrows[r2][1]
            pv2.append(c); r2 += 1
        assert r2 == d
        X = []
        for t in range(d):
            x = 0
            for i, c in enumerate(pv2):
                if (Mrows[i][1] >> t) & 1: x |= 1 << cpos[c]
            X.append(x)
        assert all((pc(X[t] & us[s]) & 1) == (t == s) for t in range(d) for s in range(d))
        good = words[q][3]
        compn = np.uint64(comp)
        for g in range(1 << d):
            x = 0
            for t in range(d):
                if (g >> t) & 1: x ^= X[t]
            mn = int(np.bitwise_count((YA ^ np.uint64(x)) & compn).min())
            if (mn >= rr) != (g in good): gmis += 1
            ncls += 1
    print(f'{ci}_{ri}: good sets recomputed for {len(sample)} words ({ncls} classes): mismatches {gmis}', flush=True)
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
