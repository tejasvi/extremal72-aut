"""Semantic check of the LTSH symmetry data sym.ltsh of a plain-C2 package (audit code).
The group G = <generators of Aut(Y) from invs.pkl> is rebuilt as a list in the builder's indexing convention
(breadth-first closure collected in a set; the indices in sym.ltsh refer to that list). Every table is then checked
against its definition, with own GF(2) coordinates:
  key line: c_i = constraint of key word k_i, m_i = dim S_{k_i};  S0 = Stab_G(k0) in G order;
  canon0[s] = min_{h in S0} s o h with (s o h)_j = <coords0(h ub0_j), s>;  s o S0[hS0[s]] = canon0[s];
  J(c) = Stab_S0(c) for every class representative c (as sets); mulS0[a][b] = index of S0[a] o S0[b];
  orbit lines (u = k0 first): c_u = constraint of u = g_u k0 (g_u = first element of G mapping k0 to u),
      t_u rows = coords_u(g_u ub0_j), comp[u][q] = index of g_u o S0[q];
  per g (r > 1): c_{g k_i} = constraint of g k_i, rows T_{g,i}[j] = coords_{g k_i}(g ub_i[j]);
  plus a direct transport test on random forms B: s_w(B^g) = T(s_{gw}(B)) with B^g(x,y) = B(gx,gy).
Usage: symcheck.py PKGDIR CI NRANDB"""
import sys, os, pickle, random
sys.path.insert(0, '<HOME>/c72/audit/c2audit/engine-check/scripts')
from indep_c2 import GF2, load_codes, CODES
M = 36; K = 18


def fail(msg):
    print('FAIL', msg, flush=True); sys.exit(2)


def closure(gens, m):           # builder's indexing convention: set-based BFS, list(set)
    idp = tuple(range(m)); seen = {idp}; fr = [idp]
    while fr:
        nf = []
        for p in fr:
            for g in gens:
                q = tuple(g[p[i]] for i in range(m))
                if q not in seen: seen.add(q); nf.append(q)
        fr = nf
    return list(seen)


def ap(p, x):
    o = 0
    while x:
        lb = x & -x; i = lb.bit_length() - 1; o |= 1 << p[i]; x ^= lb
    return o


def coords_in(basis):
    B = GF2()
    for k, b in enumerate(basis):
        ok, _ = B.add(b, 1 << k)
        if not ok: fail('dependent basis')
    def co(x):
        v, t = B.reduce(x, 0)
        if v: fail('vector not in span')
        return t
    return co


def main():
    pkg, ci, nrb = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    codes = load_codes(CODES); Y = codes[ci]
    S = [0]
    for g in Y: S = S + [s ^ g for s in S]
    Yset = set(S)
    gens = pickle.load(open('<HOME>/c72/c2par/invs.pkl', 'rb'))[ci]['perms']
    G = closure([list(g) for g in gens], M)
    gidx = {g: k for k, g in enumerate(G)}
    for g in G:
        if any(ap(g, y) not in Yset for y in Y): fail('G element not in Aut(Y)')
    meta = [list(map(int, l.split())) for l in open(os.path.join(pkg, 'inst.txt.meta')) if l.strip()]
    idx = {row[0]: k for k, row in enumerate(meta)}
    key = [int(x) for x in open(os.path.join(pkg, 'key.txt')).read().split()[1:]]
    tok = open(os.path.join(pkg, 'sym.ltsh')).read().split()
    pos = 0
    def nxt():
        nonlocal pos
        v = tok[pos]; pos += 1; return v
    if nxt() != 'LTSH': fail('tag')
    r, m0, c0, nO, nS0, nG, nCls = (int(nxt()) for _ in range(7))
    if r > len(key): fail('r > len(key)')
    key = key[:r]
    kl = [(int(nxt()), int(nxt())) for _ in range(r)]
    for i, w in enumerate(key):
        if w not in idx or kl[i] != (idx[w], len(meta[idx[w]]) - 1): fail(f'key line {i}')
    if c0 != idx[key[0]] or m0 != kl[0][1]: fail('c0/m0')
    if nG != len(G): fail(f'|G| {nG} != {len(G)}')
    canon0 = [int(nxt()) for _ in range(1 << m0)]
    hS0 = [int(nxt()) for _ in range(1 << m0)]
    cls = {}
    for _ in range(nCls):
        c = int(nxt()); n = int(nxt()); cls[c] = [int(nxt()) for _ in range(n)]
    mul = [[int(nxt()) for _ in range(nS0)] for _ in range(nS0)]
    olines = []
    for _ in range(nO):
        cu = int(nxt()); rows = [int(nxt()) for _ in range(m0)]; comp = [int(nxt()) for _ in range(nS0)]
        olines.append((cu, rows, comp))
    glines = []
    if r > 1:
        for _ in range(nG):
            parts = []
            for i in range(1, r):
                c = int(nxt()); parts.append((c, [int(nxt()) for _ in range(kl[i][1])]))
            glines.append(parts)
    if pos != len(tok): fail('trailing tokens')
    k0 = key[0]; ub0 = meta[c0][1:]; co0 = coords_in(ub0)
    S0 = [g for g in G if ap(g, k0) == k0]
    if len(S0) != nS0: fail('|S0|')
    s0idx = {g: k for k, g in enumerate(S0)}
    acts = [[co0(ap(h, ub0[j])) for j in range(m0)] for h in S0]
    def act(rows, s):
        o = 0
        for j, rr in enumerate(rows):
            if (rr & s).bit_count() & 1: o |= 1 << j
        return o
    for s in range(1 << m0):
        imgs = [act(rw, s) for rw in acts]
        if canon0[s] != min(imgs): fail(f'canon0[{s}]')
        if imgs[hS0[s]] != canon0[s]: fail(f'hS0[{s}]')
    if set(cls) != set(canon0): fail('class set')
    for c, J in cls.items():
        if sorted(J) != [k for k, rw in enumerate(acts) if act(rw, c) == c]: fail(f'J({c})')
    comp2 = lambda x, y: tuple(x[y[p]] for p in range(M))
    for a in range(nS0):
        for b in range(nS0):
            if S0[mul[a][b]] != comp2(S0[a], S0[b]): fail('mulS0')
    reps = {k0: tuple(range(M))}
    for g in G:
        u = ap(g, k0)
        if u not in reps: reps[u] = g
    order = [k0] + [u for u in reps if u != k0]
    if len(order) != nO: fail('|orbit|')
    for (cu, rows, comp), u in zip(olines, order):
        gu = reps[u]
        if cu != idx[u]: fail('c_u')
        cou = coords_in(meta[cu][1:])
        if rows != [cou(ap(gu, ub0[j])) for j in range(m0)]: fail('t_u rows')
        if comp != [gidx[comp2(gu, h)] for h in S0]: fail('comp')
    cache = {}
    for gi, parts in enumerate(glines):
        g = G[gi]
        for i, (c, rows) in enumerate(parts, start=1):
            v = ap(g, key[i])
            if c != idx[v]: fail(f'c_(g k_{i}) at g {gi}')
            if c not in cache: cache[c] = coords_in(meta[c][1:])
            ubi = meta[kl[i][0]][1:]
            if rows != [cache[c](ap(g, ubi[j])) for j in range(len(ubi))]: fail(f'T rows at g {gi} i {i}')
    # direct transport test with random forms B (any symmetric matrix; the identity does not need the diagonal rule)
    rnd = random.Random(ci)
    basis = []
    BB = GF2()
    for y in S:
        if y and BB.add(y, 1 << len(basis))[0]: basis.append(y)
        if len(basis) == K: break
    co = coords_in(basis)
    ntest = 0
    for _ in range(nrb):
        Gm = [[0] * K for _ in range(K)]
        for i in range(K):
            for j in range(i, K): Gm[i][j] = Gm[j][i] = rnd.getrandbits(1)
        def Bf(x, z):
            cx, cz = co(x), co(z); s = 0
            for i in range(K):
                if (cx >> i) & 1:
                    for j in range(K):
                        if (cz >> j) & 1: s ^= Gm[i][j]
            return s
        def syn(w, Bfun):
            return sum(Bfun(w, u) << j for j, u in enumerate(meta[idx[w]][1:]))
        for _ in range(8):
            gi = rnd.randrange(len(G)); g = G[gi]
            Bg = lambda x, z: Bf(ap(g, x), ap(g, z))
            for i, w in enumerate(key):
                gw = ap(g, w); cgw = idx[gw]
                T = [coords_in(meta[cgw][1:])(ap(g, u)) for u in meta[idx[w]][1:]]
                lhs = syn(w, Bg); rhs = act(T, syn(gw, Bf))
                if lhs != rhs: fail('transport identity')
                ntest += 1
    print(f'RESULT PASS {os.path.basename(os.path.normpath(pkg))} r {r} |G| {nG} |orbit(k0)| {nO} |S0| {nS0} classes {nCls} transport tests {ntest}', flush=True)


if __name__ == '__main__':
    main()
