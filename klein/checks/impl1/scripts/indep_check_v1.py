"""Independent re-derivation and check of a level-wise instance file lwf_CI_RI.txt (C2 x C2 case, length 72).
Does NOT import lwprep.  Inputs: the reduction data (codes36 via autinv.load, invs.pkl, group_elements,
fpf_involution_classes) and the parametrisation pickle (w, free, entf, N) stored next to the instance.
Checks
  P1  beta fpf involution in Aut(Y); Y self-dual [36,18,8], 1 in Y; w a basis of Y
  P2  every parametrised Gram matrix is beta-invariant (identity of affine forms)
  P3  every parametrised Gram matrix satisfies G_kk + B(w_k,1) = |w_k|/2 (identity of affine forms)
  P4  parametrisation injective (rank N); entry (i,j), i<=j, uses only variables of rows <= i; levels = rows
  P5  completeness modulo gauge: N + rank(Gamma) = dim S0, Lin(P) cap Gamma = 0, Gamma subset S0,
      Gamma = span{D_R (R a beta-orbit pair)} + D_T' with MY transversal T' (largest point of each orbit)
  C1  every low word y (0<|y|<=14, ALL of them, not deduplicated) has a file constraint whose kill predicate equals
      the independently derived predicate 'B(y,.) on S_y equals the class of some z, |z|<(16-|y|)/2, z outside y'
      (exact: enumeration of the joint image of both syndrome maps); every file constraint is matched by some y;
      file level = support level; file header/vstart consistent with the pickle.
Usage: indep_check.py CI RI INSTANCE PICKLE [OUT_MAP]"""
import sys, pickle, itertools, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE + '/../../../model')
from autinv import load
from v4sat import group_elements, fpf_involution_classes

M = 36; K = 18; DMIN = 16
ALL = (1 << M) - 1


class GF2:
    """Fully reduced row basis, pivot = highest bit, with tag (transform) tracking."""
    def __init__(self):
        self.rows = {}
    def reduce(self, v, tag=0):
        for b, (r, t) in self.rows.items():
            if (v >> b) & 1: v ^= r; tag ^= t
        return v, tag
    def add(self, v, tag=0):
        v, tag = self.reduce(v, tag)
        if v == 0: return False, tag
        b = v.bit_length() - 1
        for b2, (r, t) in list(self.rows.items()):
            if (r >> b) & 1: self.rows[b2] = (r ^ v, t ^ tag)
        self.rows[b] = (v, tag)
        return True, tag
    def rank(self): return len(self.rows)
    def canon(self): return tuple(sorted(r for r, t in self.rows.values()))


def apply_perm(p, x):
    o = 0
    while x:
        lb = x & -x; i = lb.bit_length() - 1; o |= 1 << p[i]; x ^= lb
    return o


def fail(msg):
    print('FAIL', msg, flush=True); sys.exit(2)


def parse_instance(fn):
    with open(fn) as f:
        N, NLEV, NC = map(int, f.readline().split())
        vs = list(map(int, f.readline().split()))
        cons = []
        for c in range(NC):
            lv, wt, m, nb = map(int, f.readline().split())
            forms = []
            for s in range(m):
                hx, cc = f.readline().split(); forms.append((int(hx, 16), int(cc)))
            line = f.readline().split()
            bad = list(map(int, line))
            assert len(bad) == nb
            cons.append((lv, wt, forms, bad))
    return N, NLEV, vs, cons


def joint_equiv(m1, F, Fbad, m2, Mf, Mbad, N):
    """Exact: for all X, [sF(X) in Fbad] == [sM(X) in Mbad].  Enumerates the joint affine image."""
    cF = 0; cM = 0
    for s, (vm, c) in enumerate(F): cF |= c << s
    for s, (vm, c) in enumerate(Mf): cM |= c << s
    B = GF2()
    rankF = GF2()
    for v in range(N):
        cv = 0
        for s, (vm, c) in enumerate(F):
            if (vm >> v) & 1: cv |= 1 << s
        fpart = cv
        for s, (vm, c) in enumerate(Mf):
            if (vm >> v) & 1: cv |= 1 << (m1 + s)
        if cv: B.add(cv)
        if fpart: rankF.add(fpart)
    basis = [r for r, t in B.rows.values()]
    if len(basis) > 22: return None, len(basis), rankF.rank()
    cur = cF | (cM << m1); maskF = (1 << m1) - 1
    nbadF = 0
    for q in range(1 << len(basis)):
        if q: cur ^= basis[(q & -q).bit_length() - 1]
        f = cur & maskF; g = cur >> m1
        a = f in Fbad; b = g in Mbad
        if a != b: return False, len(basis), rankF.rank()
        nbadF += a
    return True, len(basis), (rankF.rank(), nbadF)


def main():
    ci, ri, instf, pklf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    outmap = sys.argv[5] if len(sys.argv) > 5 else None
    t0 = time.time()
    codes = load(); res = pickle.load(open(HERE + '/../../../model/invs.pkl', 'rb'))
    Gp = group_elements(res[ci]['perms']); reps, _ = fpf_involution_classes(Gp)
    beta = list(reps[ri])
    Ygen = codes[ci]
    P = pickle.load(open(pklf, 'rb'))
    w, free, entf, N = P['w'], P['free'], P['entf'], P['N']
    # ---- P1
    if sorted(beta) != list(range(M)) or any(beta[beta[i]] != i or beta[i] == i for i in range(M)): fail('beta not fpf involution')
    Yall = [0]
    for g in Ygen: Yall = Yall + [s ^ g for s in Yall]
    Yset = set(Yall)
    if len(Yset) != 1 << K: fail('|Y|')
    if any(((a & b).bit_count() & 1) for a in Ygen for b in Ygen): fail('Y not self-orthogonal')
    if ALL not in Yset: fail('1 not in Y')
    if min(y.bit_count() for y in Yall if y) != 8: fail('d(Y) != 8')
    if any(apply_perm(beta, g) not in Yset for g in Ygen): fail('beta not in Aut(Y)')
    if len(w) != K or any(x not in Yset for x in w): fail('w not in Y')
    WB = GF2()
    for k, x in enumerate(w):
        ok, _ = WB.add(x, 1 << k)
        if not ok: fail('w dependent')
    def coords(x):
        v, t = WB.reduce(x, 0)
        if v: fail('coords')
        return t
    # ---- entries / affine forms (bit N = constant)
    E = [(i, j) for i in range(K) for j in range(i, K)]
    eidx = {e: n for n, e in enumerate(E)}
    NE = len(E)
    if len(entf) != NE: fail('entf length')
    aff = [vm | (c << N) for (vm, c) in entf]
    if any(vm >> N for vm, c in entf): fail('entf uses variable >= N')
    Gaff = [[aff[eidx[(min(a, b), max(a, b))]] for b in range(K)] for a in range(K)]
    def Bform(cx, cz):
        f = 0
        for a in range(K):
            if (cx >> a) & 1:
                for b in range(K):
                    if (cz >> b) & 1: f ^= Gaff[a][b]
        return f
    def Bmask(cx, cz):   # entry-space mask of B(x,z)
        mm = 0
        for a in range(K):
            if (cx >> a) & 1:
                for b in range(K):
                    if (cz >> b) & 1: mm ^= 1 << eidx[(min(a, b), max(a, b))]
        return mm
    bc = [coords(apply_perm(beta, w[k])) for k in range(K)]
    c1 = coords(ALL)
    # ---- P2 invariance identity, P3 diagonal identity
    for (i, j) in E:
        if Bform(bc[i], bc[j]) != Gaff[i][j]: fail(f'P2 invariance fails at {(i, j)}')
    for k in range(K):
        lhs = Gaff[k][k] ^ Bform(1 << k, c1)
        if lhs != (((w[k].bit_count() // 2) & 1) << N): fail(f'P3 diagonal fails at {k}')
    # ---- P4 injectivity, levels
    level = [E[e][0] for e in free]
    if len(free) != N or sorted(free) != free: fail('free list')
    for n, e in enumerate(free):
        if aff[e] != (1 << n): fail('free entry form')
    for e in range(NE):
        vm = aff[e] & ((1 << N) - 1)
        if vm and level[vm.bit_length() - 1] > E[e][0]: fail(f'P4 entry {E[e]} uses higher-level variable')
    R = GF2()
    for e in range(NE): R.add(aff[e] & ((1 << N) - 1))
    if R.rank() != N: fail('P4 rank')
    # ---- P5 completeness modulo gauge
    eqs = []
    for (i, j) in E: eqs.append(Bmask(bc[i], bc[j]) ^ (1 << eidx[(i, j)]))
    for k in range(K): eqs.append((1 << eidx[(k, k)]) ^ Bmask(1 << k, c1))
    EQ = GF2()
    for q in eqs: EQ.add(q)
    dimS0 = NE - EQ.rank()
    def in_S0(vec): return all(((q & vec).bit_count() & 1) == 0 for q in eqs)
    orbs = sorted({(min(p, beta[p]), max(p, beta[p])) for p in range(M)})
    def Dvec(Rset):
        v = 0
        for (i, j) in E:
            if (w[i] & w[j] & Rset).bit_count() & 1: v |= 1 << eidx[(i, j)]
        return v
    gam = [Dvec((1 << p) | (1 << q)) for (p, q) in orbs]
    Tmine = 0
    for (p, q) in orbs: Tmine |= 1 << q
    gam.append(Dvec(Tmine))
    if not all(in_S0(g) for g in gam): fail('P5 gauge vector not in S0')
    GB = GF2()
    for g in gam: GB.add(g)
    rg = GB.rank()
    cols = []
    for v in range(N):
        cv = 0
        for e in range(NE):
            if (aff[e] >> v) & 1: cv |= 1 << e
        cols.append(cv)
    if not all(in_S0(cv) for cv in cols): fail('P5 column not in S0')
    LB = GF2()
    for cv in cols: LB.add(cv)
    for g in gam: LB.add(g)
    if LB.rank() != N + rg: fail('P5 Lin(P) meets Gamma')
    if N + rg != dimS0: fail(f'P5 dimension: N {N} + rank Gamma {rg} != dim S0 {dimS0}')
    print(f'P1-P5 ok: N {N}, rank Gamma {rg}, dim S0 {dimS0}, orbits {len(orbs)}', flush=True)
    # ---- file header
    Nf, NLEV, vs, cons = parse_instance(instf)
    if Nf != N or NLEV != K: fail('header')
    vs2 = [0] * (K + 1)
    for t in range(K): vs2[t + 1] = vs2[t] + sum(1 for v in range(N) if level[v] == t)
    if vs != vs2: fail('vstart')
    if any(cons[i][0] > cons[i + 1][0] for i in range(len(cons) - 1)): fail('constraints not sorted')
    keymap = {}; ndep = 0
    for idx, (lv, wt, forms, bad) in enumerate(cons):
        B = GF2()
        for (vm, c) in forms: B.add(vm | (c << N))
        if B.rank() != len(forms): ndep += 1
        sup = 0
        for (vm, c) in forms: sup |= vm
        lvf = level[sup.bit_length() - 1] if sup else 0
        if lvf != lv: fail(f'file constraint {idx} level {lv} != support level {lvf}')
        if any(not (0 <= b < (1 << len(forms))) for b in bad) or len(set(bad)) != len(bad): fail('bad list range/dup')
        keymap.setdefault((B.canon(), wt), []).append(idx)
    print(f'file constraints {len(cons)}, with linearly dependent affine forms: {ndep}', flush=True)
    # ---- C1 per low word
    low = [y for y in Yall if y and y.bit_count() <= DMIN - 2]
    matched_by = [0] * len(cons)
    ymap = {}
    stats = {}
    nfail = 0
    for y in low:
        wy = y.bit_count(); r = (DMIN - wy) // 2
        cy = coords(y)
        yrow = [0] * K
        for b in range(K):
            f = 0
            for a in range(K):
                if (cy >> a) & 1: f ^= Gaff[a][b]
            yrow[b] = f
        KB = GF2(); ker = []
        for k in range(K):
            ok, tag = KB.add(w[k] & y, 1 << k)
            if not ok: ker.append(tag)
        us = []
        for tag in ker:
            u = 0
            for k in range(K):
                if (tag >> k) & 1: u ^= w[k]
            if u & y or u == 0: fail('shortened vector')
            us.append((u, tag))
        m = len(us)
        if m > 16 or m == 0: fail(f'm = {m}')
        Mf = []
        for (u, tag) in us:
            f = 0
            for b in range(K):
                if (tag >> b) & 1: f ^= yrow[b]
            Mf.append((f & ((1 << N) - 1), f >> N))
        cpos = [p for p in range(M) if not (y >> p) & 1]
        colp = {}
        for p in cpos:
            cv = 0
            for s, (u, tag) in enumerate(us):
                if (u >> p) & 1: cv |= 1 << s
            colp[p] = cv
        Mbad = set()
        for k in range(r):
            for sub in itertools.combinations(cpos, k):
                s = 0
                for p in sub: s ^= colp[p]
                Mbad.add(s)
        B = GF2()
        for (vm, c) in Mf: B.add(vm | (c << N))
        key = (B.canon(), wy)
        cands = keymap.get(key, [])
        hit = None
        for idx in cands:
            lv, wt, forms, bad = cons[idx]
            ok, rk, info = joint_equiv(len(forms), forms, set(bad), m, Mf, Mbad, N)
            if ok:
                hit = idx; break
        if hit is None:
            nfail += 1
            if nfail < 10: print('NO MATCH for y', hex(y), 'weight', wy, 'cands', len(cands), flush=True)
            continue
        matched_by[hit] += 1
        ymap[y] = hit
        st = stats.setdefault(wy, [0, 0, 0])
        st[0] += 1; st[1] += len(Mbad); st[2] += m
    nunmatched = sum(1 for x in matched_by if x == 0)
    print(f'low words {len(low)}, unmatched words {nfail}, file constraints {len(cons)}, file constraints not matched {nunmatched}', flush=True)
    from collections import Counter
    print('matches per file constraint:', dict(Counter(matched_by)), flush=True)
    for wy in sorted(stats): print(f'  weight {wy}: words {stats[wy][0]}, mean |bad| {stats[wy][1] / stats[wy][0]:.1f}, mean m {stats[wy][2] / stats[wy][0]:.2f}', flush=True)
    # beta-orbit consistency: y and beta y matched to the same file constraint
    nb = sum(1 for y in ymap if ymap.get(apply_perm(beta, y)) != ymap[y])
    print('words whose beta-image maps to a different constraint:', nb, flush=True)
    if outmap:
        cmap = {}
        for y, idx in ymap.items(): cmap.setdefault(idx, []).append(y)
        pickle.dump(dict(ci=ci, ri=ri, beta=beta, cmap=cmap), open(outmap, 'wb'))
    verdict = (nfail == 0 and nunmatched == 0)
    print('RESULT', 'PASS' if verdict else 'FAIL', f'{ci}_{ri}', f'time {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
