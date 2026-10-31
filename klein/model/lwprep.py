"""Level-wise (Gram-row) instance for a C2 x C2 case (Y, bb).
B is written as its Gram matrix G[i][j] = B(w_i, w_j) in a chosen basis w of Y.  Valid B: bb-invariant, symmetric,
G[k][k] = |w_k|/2 + B(w_k, 1); normalised modulo the gauge span{D_R (R a bb-orbit of pairs), D_T (T one pair
from every bb-orbit)} by fixing gauge pivot entries to 0.  Free variables = non-pivot entries of the reverse-order
reduced echelon form, so every entry G[i][j] (i <= j) is an affine form in free entries of rows <= i; a free entry
of row t is a level-t variable.  Constraint word y (|y| <= d-2, one per bb-orbit): syndrome bits B(y, u_s) over the
shortened code basis, affine in variables; level = highest variable level occurring.
Output: text file for lwe.c.  Usage: lwprep.py CI RI OUT [m d]  (or control mode via import)."""
import sys, itertools, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from v4sat import group_elements, fpf_involution_classes, applym, pc


def span_list(gens):
    S = [0]
    for g in gens: S = S + [s ^ g for s in S]
    return S


def coords_solver(basis):
    piv = {}
    for k, b in enumerate(basis):
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
    return coords


def build(Ygens, bb, m=36, d=16, order='greedy', verbose=True):
    K = m // 2
    ALL = (1 << m) - 1
    Yall = span_list(Ygens)
    assert len(set(Yall)) == 1 << K
    low = [y for y in Yall if y and pc(y) <= d - 2]
    # basis order: greedy, maximise number of low words in the span (ties: lower weight)
    lowset = set(low)
    if order == 'fixedfirst':
        fixed = [y for y in Yall if applym(bb, y, m) == y]
        w = []; spanset = {0}
        fixlow = [y for y in fixed if y and pc(y) <= d - 2] or [y for y in fixed if y]
        fixset = set(fixed)
        while True:
            cands = [y for y in fixed if y and y not in spanset]
            if not cands: break
            best = None
            for y in cands:
                new = sum(1 for s in spanset if (s ^ y) in lowset)
                key = (new, -pc(y))
                if best is None or key > best[0]: best = (key, y)
            y = best[1]; w.append(y); spanset = spanset | {s ^ y for s in spanset}
        while len(w) < K:
            best = None
            cands = [y for y in low if y not in spanset] or [y for y in Yall if y not in spanset]
            for y in cands[:4000]:
                new = sum(1 for s in spanset if (s ^ y) in lowset)
                key = (new, -pc(y))
                if best is None or key > best[0]: best = (key, y)
            y = best[1]; w.append(y); spanset = spanset | {s ^ y for s in spanset}
    elif order == 'greedy':
        w = []; spanset = {0}
        while len(w) < K:
            best = None
            cands = [y for y in low if y not in spanset] or [y for y in Yall if y not in spanset]
            for y in cands[:4000]:
                new = sum(1 for s in spanset if (s ^ y) in lowset)
                key = (new, -pc(y))
                if best is None or key > best[0]: best = (key, y)
            y = best[1]; w.append(y); spanset = spanset | {s ^ y for s in spanset}
    else:
        w = list(order)
    coords = coords_solver(w)
    # entries (i<=j) indexed row-major
    E = [(i, j) for i in range(K) for j in range(i, K)]
    eix = {e: n for n, e in enumerate(E)}
    def ei(i, j): return eix[(i, j) if i <= j else (j, i)]
    NE = len(E)
    def form_mask(ci, cj):   # B(sum_i ci w_i, sum_j cj w_j) as entry mask
        mm = 0
        for i in range(K):
            if (ci >> i) & 1:
                for j in range(K):
                    if (cj >> j) & 1: mm ^= 1 << ei(i, j)
        return mm
    eqs = []
    if bb is not None:
        bc = [coords(applym(bb, w[k], m)) for k in range(K)]
        for (i, j) in E:                                     # invariance
            eqs.append((form_mask(bc[i], bc[j]) ^ (1 << ei(i, j)), 0))
    cone = coords(ALL)
    for k in range(K):                                       # diagonal (doubly even)
        mm = (1 << ei(k, k)) ^ form_mask(1 << k, cone)
        if mm: eqs.append((mm, (pc(w[k]) // 2) & 1))
        else: assert (pc(w[k]) // 2) % 2 == 0
    # gauge vectors
    orbs = []; seen = set()
    if bb is not None:
        for p in range(m):
            if p in seen: continue
            orbs.append((p, bb[p])); seen |= {p, bb[p]}
    def Dset(R):
        mm = 0
        for (i, j) in E:
            if pc(w[i] & w[j] & R) & 1: mm |= 1 << ei(i, j)
        return mm
    if bb is not None:
        gauge = [Dset((1 << p) | (1 << q)) for (p, q) in orbs]
        T = 0
        for (p, q) in orbs: T |= 1 << p
        gauge.append(Dset(T))
    else:
        gauge = [Dset(1 << p) for p in range(m)]
    # gauge pivots: earliest entries (row-major = lowest index) via elimination with lowest-bit pivots
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
    for b in gp: eqs.append((1 << b, 0))                     # fix gauge pivot entries to 0
    # reverse-order RREF: pivot = highest entry index
    piv = {}
    for mm, r in eqs:
        for b in sorted(piv, reverse=True):
            if (mm >> b) & 1: mm ^= piv[b][0]; r ^= piv[b][1]
        if not mm:
            assert r == 0, "inconsistent"
            continue
        b = mm.bit_length() - 1
        for b2 in list(piv):
            if (piv[b2][0] >> b) & 1: piv[b2] = (piv[b2][0] ^ mm, piv[b2][1] ^ r)
        piv[b] = (mm, r)
    free = [e for e in range(NE) if e not in piv]
    N = len(free)
    # order free variables by (row, index); level = row
    free.sort()
    vidx = {e: n for n, e in enumerate(free)}
    level = [E[e][0] for e in free]
    # entry -> affine form over variables (mask over N, const)
    entf = []
    for e in range(NE):
        if e in vidx: entf.append((1 << vidx[e], 0))
        else:
            mm, r = piv[e]
            vm = 0
            for b in range(NE):
                if b != e and (mm >> b) & 1:
                    assert b in vidx and b < e
                    vm |= 1 << vidx[b]
            entf.append((vm, r))
    for e in range(NE):   # check: entry forms only use variables of levels <= its row
        vm, _ = entf[e]
        for v in range(N):
            if (vm >> v) & 1: assert level[v] <= E[e][0]
    # constraints
    def entry_comb_to_form(emask):
        vm = 0; c = 0
        for e in range(NE):
            if (emask >> e) & 1: vm ^= entf[e][0]; c ^= entf[e][1]
        return vm, c
    lowdone = set(); cons = []
    for y in low:
        if y in lowdone: continue
        lowdone.add(y)
        if bb is not None: lowdone.add(applym(bb, y, m))
        r = (d - pc(y)) // 2
        # shortened basis: Y words disjoint from y (basis via elimination)
        sh = [u for u in Yall if u & y == 0]
        ub = []
        red = []
        for u in sh:
            v = u
            for x in red: v = min(v, v ^ x)
            if v: red.append(v); ub.append(u)
        cpos = [i for i in range(m) if not (y >> i) & 1]
        bad = set()
        for wt in range(0, r):
            for sub in itertools.combinations(cpos, wt):
                z = 0
                for i in sub: z |= 1 << i
                cls = 0
                for t, u in enumerate(ub):
                    if pc(z & u) & 1: cls |= 1 << t
                bad.add(cls)
        cy = coords(y)
        forms = [entry_comb_to_form(form_mask(cy, coords(u))) for u in ub]
        lv = max([level[v] for (vm, c) in forms for v in range(N) if (vm >> v) & 1] or [0])
        cons.append((lv, pc(y), forms, sorted(bad)))
    nlev = K
    if verbose:
        kt = [sum(1 for v in range(N) if level[v] == t) for t in range(nlev)]
        print(f"  N = {N} (gauge rank {grank}), k_t = {kt}, constraints {len(cons)}, per level "
              f"{[sum(1 for c in cons if c[0] == t) for t in range(nlev)]}", flush=True)
    return dict(N=N, level=level, cons=cons, nlev=nlev, w=w, free=free, E=E, entf=entf, grank=grank)


def export(L, fn):
    N = L['N']; nlev = L['nlev']; level = L['level']
    vstart = [0] * (nlev + 1)
    for t in range(nlev): vstart[t + 1] = vstart[t] + sum(1 for v in range(N) if level[v] == t)
    assert all(level[v] <= level[v + 1] for v in range(N - 1))
    out = [f"{N} {nlev} {len(L['cons'])}", ' '.join(map(str, vstart))]
    for (lv, wt, forms, bad) in sorted(L['cons'], key=lambda c: c[0]):
        out.append(f"{lv} {wt} {len(forms)} {len(bad)}")
        for (vm, c) in forms: out.append(f"{vm:x} {c}")
        out.append(' '.join(map(str, bad)))
    open(fn, 'w').write('\n'.join(out) + '\n')


if __name__ == '__main__':
    from autinv import load
    ci, ri, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    codes = load(); res = pickle.load(open(HERE + '/invs.pkl', 'rb'))
    G = group_elements(res[ci]['perms']); reps, _ = fpf_involution_classes(G)
    L = build(codes[ci], list(reps[ri]), order=(sys.argv[4] if len(sys.argv) > 4 else 'greedy'))
    export(L, fn)
    pickle.dump(dict(w=L['w'], free=L['free'], entf=L['entf'], N=L['N']), open(fn + '.pkl', 'wb'))
