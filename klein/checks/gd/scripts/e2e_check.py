"""End-to-end semantic check of a C2xC2 instance file (independent of the solver and of the bad-set code).
1. regenerate the instance with v4sat/v4export and compare bytes with inst/v4_ci_ri.txt
2. own parser of the instance file
3. independent dimension count of the valid-B space (own linear algebra) vs nW + swap rank
4. for random w: B(w) = part + sum w_t W_t; build C (72 bits) with own dual basis; check self-dual, doubly even,
   alpha- and beta-invariant; for every low word y (and its bb image) compute the true min weight of the coset
   v(y,z0(y)) + pi^-1(Y) by brute force over the 2^18 words of Y; compare 'min>=16' with the instance verdict."""
import sys, os, pickle, random, hashlib, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np
sys.path.insert(0, HERE + '/../../../model')
from v4sat import setup, group_elements, fpf_involution_classes
from autinv import load as load_v4
from v4export import export
M = 36; K = 18
def pc(x): return bin(x).count('1')
def own_load():
    blocks = open(HERE + '/../../../codes36.txt').read().strip().split('\n\n')
    return [[int(r.strip()[::-1], 2) for r in b.strip().split('\n') if r.strip()] for b in blocks]
def parse_inst(fn):
    tok = open(fn).read().split('\n')
    nW, nwords = map(int, tok[0].split()); p = 1; words = []
    for _ in range(nwords):
        wt, d, ng = map(int, tok[p].split()); p += 1
        forms = []
        for t in range(d):
            m, c = tok[p].split(); p += 1; forms.append((int(m, 16), int(c)))
        good = set(map(int, tok[p].split())) if ng else set(); p += 1
        assert len(good) == ng
        words.append((wt, d, forms, good))
    return nW, words
def rank_list(vs):
    piv = {}
    for v in vs:
        while v:
            h = v.bit_length() - 1
            if h in piv: v ^= piv[h]
            else: piv[h] = v; break
    return len(piv)
def main(ci, ri, ntrials, seed):
    codes = load_v4(); res = pickle.load(open(HERE + '/../../../model/invs.pkl', 'rb'))
    assert [sorted(c) for c in codes] == [sorted(c) for c in own_load()]
    G = group_elements(res[ci]['perms']); reps, _ = fpf_involution_classes(G); bb = list(reps[ri])
    assert all(bb[bb[i]] == i and bb[i] != i for i in range(M))
    S = setup(codes[ci], bb, verbose=False)
    tmp = f'/tmp/e2e_{ci}_{ri}_{os.getpid()}.txt'; export(S, tmp)
    same = open(tmp, 'rb').read() == open(f'{HERE}/../../../gd_runs/inst/v4_{ci}_{ri}.txt', 'rb').read()
    os.remove(tmp)
    print(f'instance {ci}_{ri}: regenerated file identical: {same}', flush=True)
    nW, words = parse_inst(f'{HERE}/../../../gd_runs/inst/v4_{ci}_{ri}.txt')
    assert nW == S['nW']
    basis = S['basis']; assert basis[0] == (1 << M) - 1
    Yset = set(); Ylist = [0]
    for b in basis: Ylist = Ylist + [x ^ b for x in Ylist]
    Yset = set(Ylist); assert len(Yset) == 1 << K
    # Y must be the code
    assert Yset == set(itertools.chain([0])) | Yset
    Yorig = [0]
    for g in codes[ci]: Yorig = Yorig + [x ^ g for x in Yorig]
    assert set(Yorig) == Yset
    def ap(perm, w):
        o = 0
        for i in range(M):
            if (w >> i) & 1: o |= 1 << perm[i]
        return o
    assert all(ap(bb, x) in Yset for x in basis)
    # coefficient map (own): solve x = sum c_k b_k via elimination
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
            h = x.bit_length() - 1
            pv, pcf = piv[h]; x ^= pv; c ^= pcf
        return c
    for k, b in enumerate(basis): assert coef(b) == 1 << k
    # ---- 3. independent dimension of the space of valid homogeneous B (symmetric, bb-invariant, B(y,y)=B(y,1)) ----
    ent = {}; n = 0
    for i in range(K):
        for j in range(i, K): ent[(i, j)] = n; n += 1
    E = lambda i, j: ent[(min(i, j), max(i, j))]
    Mb = [coef(ap(bb, b)) for b in basis]
    rowsH = []
    for i in range(K):
        for j in range(i, K):
            r = 1 << E(i, j)
            for l in range(K):
                if (Mb[i] >> l) & 1:
                    for l2 in range(K):
                        if (Mb[j] >> l2) & 1: r ^= 1 << E(l, l2)
            rowsH.append(r)
    for k in range(1, K): rowsH.append((1 << E(k, k)) ^ (1 << E(0, k)))
    rk = rank_list(rowsH); dimV = n - rk
    # swap deltas
    seen = set(); deltas = []
    for p in range(M):
        if p in seen: continue
        R = (1 << p) | (1 << bb[p]); seen |= {p, bb[p]}
        dv = 0
        for i in range(K):
            for j in range(i, K):
                if pc(basis[i] & basis[j] & R) & 1: dv |= 1 << E(i, j)
        deltas.append(dv)
    rD = rank_list(deltas)
    # W must lie in V, W + deltas must span V, part must satisfy the inhomogeneous system
    def inV(v): return all(pc(r & v) % 2 == 0 for r in rowsH)
    Wv = S['W']; part = S['part']
    assert S['E'] == [(i, j) for i in range(K) for j in range(i, K)]
    okW = all(inV(w) for w in Wv) and all(inV(d) for d in deltas)
    span_ok = rank_list(Wv + deltas) == dimV and rank_list(Wv) == len(Wv)
    rhs_ok = all(pc(rowsH[t] & part) % 2 == 0 for t in range(len(rowsH) - (K - 1))) and \
             all(((part >> E(k, k)) & 1) ^ ((part >> E(0, k)) & 1) == (pc(basis[k]) // 2) % 2 for k in range(1, K))
    print(f'  dimV={dimV} swap rank={rD} nW={nW} (dimV-rank={dimV - rD}); W in V & deltas in V: {okW}; '
          f'W+deltas span V: {span_ok}; part valid: {rhs_ok}', flush=True)
    # low words coverage
    low = [x for x in Ylist if x and pc(x) <= 14]
    lowset = set(low)
    # instance words carry only (wt,d,forms,good): recover y for each instance word from S['recs'] order (sorted by pc)
    recs = sorted(S['recs'], key=lambda r: pc(r[0]))
    ys = [r[0] for r in recs]
    assert [pc(y) for y in ys] == [w[0] for w in words]
    orbit_cover = set(ys) | set(ap(bb, y) for y in ys)
    print(f'  low words {len(low)}, instance words {len(ys)}, orbit cover == all low words: {orbit_cover == lowset}', flush=True)
    # dual basis D_j with <D_j, b_i> = delta_ij  (own Gaussian elimination on the 18x36 system)
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
    assert all(pc(D[j] & basis[i]) % 2 == (i == j) for i in range(K) for j in range(K))
    def spread(x):  # pi^-1 : 36 -> 72 bits as python int
        v = 0
        for i in range(M):
            if (x >> i) & 1: v |= 3 << (2 * i)
        return v
    def vyz(y, z):
        v = 0
        for i in range(M):
            zi = (z >> i) & 1; yi = (y >> i) & 1
            if zi: v |= 1 << (2 * i)
            if zi ^ yi: v |= 1 << (2 * i + 1)
        return v
    SP = [spread(x) for x in Ylist]
    XL = np.array([s & ((1 << 64) - 1) for s in SP], dtype=np.uint64)
    XH = np.array([s >> 64 for s in SP], dtype=np.uint64)
    alpha = [i ^ 1 for i in range(72)]
    beta = [0] * 72
    for i in range(M): beta[2 * i] = 2 * bb[i]; beta[2 * i + 1] = 2 * bb[i] + 1
    def ap72(perm, w):
        o = 0
        for i in range(72):
            if (w >> i) & 1: o |= 1 << perm[i]
        return o
    rng = random.Random(seed)
    tot_good = tot_bad = mism = 0
    for trial in range(ntrials):
        w = rng.getrandbits(nW)
        vec = part
        for t in range(nW):
            if (w >> t) & 1: vec ^= Wv[t]
        B = [[(vec >> E(i, j)) & 1 for j in range(K)] for i in range(K)]
        z0b = []
        for k in range(K):
            z = 0
            for j in range(K):
                if B[k][j]: z ^= D[j]
            z0b.append(z)
        gens = [vyz(basis[k], z0b[k]) for k in range(K)] + [spread(b) for b in basis]
        # C checks: rank 36, self-orthogonal, doubly even generators, alpha/beta invariance
        assert rank_list(gens) == 36
        so = all(pc(a & b) % 2 == 0 for a in gens for b in gens)
        de = all(pc(a) % 4 == 0 for a in gens)
        def inC(v):
            return rank_list(gens + [v]) == 36
        ainv = all(inC(ap72(alpha, g)) for g in gens); binv = all(inC(ap72(beta, g)) for g in gens)
        print(f'  trial {trial}: C self-orthogonal {so}, doubly-even gens {de}, alpha-inv {ainv}, beta-inv {binv}', flush=True)
        def z0(y):
            c = coef(y); z = 0
            for k in range(K):
                if (c >> k) & 1: z ^= z0b[k]
            return z
        def truemin(y):
            v = vyz(y, z0(y))
            vl = np.uint64(v & ((1 << 64) - 1)); vh = np.uint64(v >> 64)
            return int((np.bitwise_count(XL ^ vl) + np.bitwise_count(XH ^ vh)).min())
        ng = nb = mm = 0
        idx = list(range(len(ys)))
        for q in idx:
            wt, d, forms, good = words[q]
            g = 0
            for t, (m, c) in enumerate(forms):
                g |= ((pc(m & w) & 1) ^ c) << t
            ver = g in good
            y = ys[q]
            tm = truemin(y)
            tm2 = truemin(ap(bb, y))
            if tm != tm2: print('   beta-image min differs!', y, tm, tm2)
            if ver != (tm >= 16):
                mm += 1
                if mm <= 5: print(f'   MISMATCH word {q} |y|={wt} instance good={ver} true min={tm}')
            if ver: ng += 1
            else: nb += 1
        print(f'  trial {trial}: words good {ng}, bad {nb}, mismatches {mm}', flush=True)
        tot_good += ng; tot_bad += nb; mism += mm
    print(f'RESULT {ci}_{ri}: regenerated identical {same}, total good {tot_good} bad {tot_bad} mismatches {mism}', flush=True)
if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
