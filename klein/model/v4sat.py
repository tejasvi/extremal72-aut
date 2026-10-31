"""SAT formulation of the C2 x C2 case.
V4 = <alpha, beta> <= Aut(C), all involutions fixed-point-free (Bouyuklieva), so V4 acts freely on the 72
coordinates.  Model (as for C2): pairs = alpha-orbits, Y = pi(C(alpha)) one of the 41 self-dual [36,18,8] codes,
C = { v(y,z) : y in Y, z in z0(y) + Y },  v(y,z)_pair i = (z_i, z_i + y_i),  <z0(y), y'> = B(y, y'),
B symmetric with B(y,y) = |y|/2 + B(y,1).  beta permutes the alpha-pairs by an fpf involution bb in Aut(Y); after
relabelling inside pairs (commutes with alpha) beta preserves positions, and then
      beta in Aut(C)  <=>  B(bb y, bb y') = B(y, y')  for all y, y' in Y.
Remaining normalisation: swaps inside the pairs of a bb-orbit (commute with alpha and beta) change
B by D_R(y,y') = |y & y' & R|.  Free part of B = W, a complement of span(D_R) in the space of valid B.
d(C) >= 16  <=>  for every y in Y with 0 < |y| <= 14 the class of B(y,.) on Y^short_y is 'good'."""
import sys, itertools, time, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from autinv import load, span, rank, apply

M36 = 36; K = 18; DMIN = 16


def pc(x): return bin(x).count('1')


def applym(perm, w, m):
    out = 0
    for i in range(m):
        if (w >> i) & 1: out |= 1 << perm[i]
    return out


def group_elements(gens, limit=10 ** 6):
    idp = tuple(range(M36))
    seen = {idp}; frontier = [idp]
    while frontier:
        nf = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[i]] for i in range(M36))
                if q not in seen:
                    seen.add(q); nf.append(q)
        frontier = nf
        if len(seen) > limit: raise RuntimeError('group too large')
    return seen


def fpf_involution_classes(G):
    inv = lambda p: tuple(sorted(range(M36), key=lambda i: p[i]))
    invs = [p for p in G if all(p[p[i]] == i for i in range(M36)) and all(p[i] != i for i in range(M36))]
    reps = []; done = set()
    Gl = list(G)
    for t in invs:
        if t in done: continue
        reps.append(t)
        for g in Gl:
            gi = inv(g)
            c = tuple(g[t[gi[i]]] for i in range(M36))
            done.add(c)
    return reps, len(invs)


def f2_solve(rows, nvar):
    """rows: list of (mask over nvar bits, rhs bit). returns (particular, nullspace basis) or None."""
    piv = {}
    for mask, rhs in rows:
        for c, (pm, pr) in piv.items():
            if (mask >> c) & 1: mask ^= pm; rhs ^= pr
        if mask == 0:
            if rhs: return None
            continue
        c = mask.bit_length() - 1
        # eliminate c from existing pivots
        for c2 in list(piv):
            pm, pr = piv[c2]
            if (pm >> c) & 1: piv[c2] = (pm ^ mask, pr ^ rhs)
        piv[c] = (mask, rhs)
    part = 0
    for c, (pm, pr) in piv.items():
        if pr: part |= 1 << c
    free = [c for c in range(nvar) if c not in piv]
    basis = []
    for f in free:
        v = 1 << f
        for c, (pm, pr) in piv.items():
            if (pm >> f) & 1: v |= 1 << c
        basis.append(v)
    return part, basis


def setup(Ygens, bb, verbose=True, m=36, d=16):
    M36 = m; K = m // 2; DMIN = d
    ALL = (1 << M36) - 1
    red = [ALL]; basis = [ALL]
    for g in Ygens:
        r = g
        for b in red: r = min(r, r ^ b)
        if r: basis.append(g); red.append(r)
    assert len(basis) == K
    coef = {0: 0}; v = 0; mm = 0
    for t in range(1, 1 << K):
        i = (t & -t).bit_length() - 1
        mm ^= 1 << i; v ^= basis[i]; coef[v] = mm
    words = list(coef.keys())
    # entries
    E = [(i, j) for i in range(K) for j in range(i, K)]
    eidx = {e: n for n, e in enumerate(E)}
    def ei(i, j): return eidx[(i, j) if i <= j else (j, i)]
    NE = len(E)
    Mb = [coef[applym(bb, basis[k], M36)] for k in range(K)]      # bb(b_k) = sum_l bit l of Mb[k] * b_l
    rows = []
    for k in range(1, K):                                    # diagonal: x_kk + x_0k = |b_k|/2
        rows.append(((1 << ei(k, k)) ^ (1 << ei(0, k)), (pc(basis[k]) // 2) & 1))
    for (i, j) in E:                                         # invariance
        mask = 1 << ei(i, j)
        for l in range(K):
            if not (Mb[i] >> l) & 1: continue
            for l2 in range(K):
                if (Mb[j] >> l2) & 1: mask ^= 1 << ei(l, l2)
        rows.append((mask, 0))
    sol = f2_solve(rows, NE)
    assert sol is not None
    part, Vb = sol
    # swap deltas over bb-orbits of coordinates
    orbits = []; seen = set()
    for p in range(M36):
        if p in seen: continue
        R = (1 << p) | (1 << bb[p]); seen |= {p, bb[p]}; orbits.append(R)
    deltas = []
    for R in orbits:
        d = 0
        for (i, j) in E:
            if pc(basis[i] & basis[j] & R) & 1: d |= 1 << ei(i, j)
        deltas.append(d)
    # check deltas in V (homogeneous solutions)
    for d in deltas:
        for mask, rhs in rows:
            assert pc(mask & d) % 2 == 0, "delta violates constraints"
    # complement W of span(deltas) inside span(Vb)
    span_piv = {}
    def reduce(vv, pv):
        for c in sorted(pv, reverse=True):
            if (vv >> c) & 1: vv ^= pv[c]
        return vv
    for d in deltas:
        r = reduce(d, span_piv)
        if r: span_piv[r.bit_length() - 1] = r
    rd = len(span_piv)
    W = []
    allp = dict(span_piv)
    for vb in Vb:
        r = reduce(vb, allp)
        if r:
            allp[r.bit_length() - 1] = r; W.append(r)
    part = reduce(part, span_piv)
    nW = len(W)
    # entry -> (set of W-vars, const)
    def entry(i, j):
        n = ei(i, j)
        vs = frozenset(t + 1 for t in range(nW) if (W[t] >> n) & 1)
        return vs, (part >> n) & 1
    # constraints per low word (one per bb-orbit of words)
    def kernel_coef(y):
        pos = [i for i in range(M36) if (y >> i) & 1]
        redl = []; kern = []
        for i in range(K):
            r = 0
            for t, p in enumerate(pos):
                if (basis[i] >> p) & 1: r |= 1 << t
            c = 1 << i
            for (pr, pc_, bit) in redl:
                if (r >> bit) & 1: r ^= pr; c ^= pc_
            if r == 0: kern.append(c)
            else: redl.append((r, c, r.bit_length() - 1))
        return kern
    low = [w for w in words if w and pc(w) <= DMIN - 2]
    lowset = set(); recs = []
    for y in low:
        if y in lowset: continue
        lowset.add(y); lowset.add(applym(bb, y, M36))
        r = (DMIN - pc(y)) // 2
        sbc = kernel_coef(y)
        us = []
        for c in sbc:
            u = 0
            for i in range(K):
                if (c >> i) & 1: u ^= basis[i]
            us.append(u)
        cpos = [i for i in range(M36) if not (y >> i) & 1]
        bad = set()
        for wt in range(0, r):
            for sub in itertools.combinations(cpos, wt):
                w = 0
                for i in sub: w |= 1 << i
                cls = 0
                for t, u in enumerate(us):
                    if pc(w & u) & 1: cls |= 1 << t
                bad.add(cls)
        cy = coef[y]; bits = []
        for s in sbc:
            vs = set(); const = 0
            for i in range(K):
                if not (cy >> i) & 1: continue
                for j in range(K):
                    if not (s >> j) & 1: continue
                    evs, ec = entry(i, j)
                    vs ^= set(evs); const ^= ec
            bits.append((frozenset(vs), const))
        recs.append((y, sbc, bits, bad))
    if verbose:
        print(f"  dim valid-B space {len(Vb)}, swap rank {rd}, free bits {nW}, low words {len(low)} "
              f"({len(recs)} up to bb)", flush=True)
    return dict(basis=basis, coef=coef, words=words, W=W, part=part, entry=entry, recs=recs, nW=nW, bb=bb, E=E, ei=ei)


def solve(S, verbose=True, timeout=None):
    import pycryptosat
    s = pycryptosat.Solver(threads=1, time_limit=timeout) if timeout else pycryptosat.Solver(threads=1)
    nv = S['nW']; aux = {}; nxt = [nv + 1]
    def auxvar(vs, const):
        key = (vs, const)
        if key in aux: return aux[key]
        a = nxt[0]; nxt[0] += 1; aux[key] = a
        s.add_xor_clause([a] + sorted(vs), bool(const))
        return a
    ncl = 0
    for (y, sbc, bits, bad) in S['recs']:
        lits = []
        for (vs, const) in bits:
            lits.append(('a', auxvar(vs, const)) if vs else ('c', const))
        for c in bad:
            clause = []; sat = False
            for t, (kind, val) in enumerate(lits):
                ct = (c >> t) & 1
                if kind == 'c':
                    if val != ct: sat = True; break
                else: clause.append(val if ct == 0 else -val)
            if sat: continue
            if not clause:
                if verbose: print("  trivially UNSAT", flush=True)
                return 'UNSAT', None
            s.add_clause(clause); ncl += 1
    if verbose: print(f"  aux {len(aux)}, clauses {ncl}", flush=True)
    t0 = time.time()
    sat, model = s.solve()
    if verbose: print(f"  solve: {sat} in {time.time() - t0:.1f}s", flush=True)
    if sat is None: return 'UNKNOWN', None
    return ('SAT' if sat else 'UNSAT'), (model if sat else None)


if __name__ == '__main__':
    codes = load()
    res = pickle.load(open(HERE + '/invs.pkl', 'rb'))
    which = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else range(41)
    tl = float(sys.argv[2]) if len(sys.argv) > 2 else None
    for ci in which:
        G = group_elements(res[ci]['perms'])
        reps, ninv = fpf_involution_classes(G)
        print(f"code {ci}: |Aut| = {len(G)}, fpf involutions {ninv} in {len(reps)} classes", flush=True)
        for ri, bb in enumerate(reps):
            t0 = time.time()
            S = setup(codes[ci], bb)
            st, model = solve(S, timeout=tl)
            print(f"RESULT code {ci} class {ri}: {st} ({time.time() - t0:.0f}s)", flush=True)
