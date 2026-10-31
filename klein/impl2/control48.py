"""Positive control: extended QR code of length 48 with a freely acting Klein four-group."""
import sys, json, subprocess, time, random, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import dreadnaut_aut, apply_perm_vec, is_aut
from fpfclasses import closure, compose, inverse
from instance import Instance
from order import best_order
from export import *
import numpy as np

def qr48():
    p = 47
    Q = sorted(set((x * x) % p for x in range(1, p)))
    best = None
    for base in (Q, [0] + Q, [x for x in range(1, p) if x not in Q], [0] + [x for x in range(1, p) if x not in Q]):
        rows = []
        for s in range(p):
            v = 0
            for q in base:
                v |= 1 << ((q + s) % p)
            # extend by parity
            if popcount(v) % 2:
                v |= 1 << p
            rows.append(v)
        B = echelon(rows)
        if len(B) == 24:
            so = all(dot(x, y) == 0 for x in B for y in B)
            if so:
                wd = weight_distribution(B, 48)
                d = min(i for i in range(1, 49) if wd[i])
                if d == 12 and all(popcount(x) % 4 == 0 for x in B):
                    best = B
                    break
    assert best is not None
    return best

def main():
    C = qr48()
    wd = weight_distribution(C, 48)
    print("QR48: dim", len(C), "weight distribution", {i: int(wd[i]) for i in range(49) if wd[i]}, flush=True)
    # PSL(2,47) on the projective line {0..46, inf=47}: x->x+1, x->4x (4 = 2^2 generates the squares), x->-1/x
    p = 47
    inf = 47
    def mk(f):
        return tuple(f(x) for x in range(48))
    def tr(x):
        return inf if x == inf else (x + 1) % p
    sqs = sorted(set((x * x) % p for x in range(1, p)))
    gsq = next(g for g in sqs if len(set(pow(g, e, p) for e in range(1, 24))) == 23)
    def mul(x):
        return inf if x == inf else (gsq * x) % p
    def inv(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return (-pow(x, p - 2, p)) % p
    gens = [mk(tr), mk(mul), mk(inv)]
    for g in gens:
        assert is_aut(list(g), C, 48), "generator is not an automorphism"
    print("PSL(2,47) generators verified as automorphisms of QR48", flush=True)
    G = closure([tuple(g) for g in gens], 48)
    assert len(G) == 47 * 48 * 46 // 2
    print("group enumerated:", len(G))
    e = tuple(range(48))
    invs = [g for g in G if g != e and compose(g, g) == e]
    print("involutions:", len(invs), "all fpf:", all(all(g[i] != i for i in range(48)) for g in invs))
    # Klein four subgroups (as frozensets)
    V4s = set()
    for a in invs:
        for b in invs:
            if a < b and compose(a, b) == compose(b, a):
                V4s.add(frozenset([a, b, compose(a, b)]))
    print("Klein four-subgroups:", len(V4s))
    # conjugacy classes of V4s
    gl = [tuple(g) for g in gens]
    rem = set(V4s)
    classes = []
    while rem:
        V = next(iter(rem))
        orb = {V}; fr = [V]
        while fr:
            nf = []
            for X in fr:
                for s in gl:
                    si = inverse(s)
                    Y = frozenset(compose(compose(si, x), s) for x in X)
                    if Y not in orb:
                        orb.add(Y); nf.append(Y)
            fr = nf
        rem -= orb
        classes.append((V, len(orb)))
    print("V4 conjugacy classes:", [sz for _, sz in classes], flush=True)
    results = []
    for ci, (V, sz) in enumerate(classes):
        for ai, a in enumerate(sorted(V)):
            b = [x for x in sorted(V) if x != a][0]
            results.append(run_control(C, a, b, "c%d_a%d" % (ci, ai)))
    json.dump(results, open(HERE + '/control48_results.json', 'w'), indent=1)
    print("CONTROL SUMMARY:", json.dumps(results))

def run_control(C, a, b, tag):
    n = 48; n2 = 24
    # pairs of a; representatives chosen so that b maps reps to reps
    pairs = []
    seen = set()
    for i in range(n):
        if i not in seen:
            pairs.append((i, a[i])); seen |= {i, a[i]}
    pair_of = {}
    for j, (x, y) in enumerate(pairs):
        pair_of[x] = j; pair_of[y] = j
    rep = [None] * n2
    for j in range(n2):
        if rep[j] is None:
            rep[j] = pairs[j][0]
            jb = pair_of[b[rep[j]]]
            assert jb != j
            rep[jb] = b[rep[j]]
    beta = [pair_of[b[rep[j]]] for j in range(n2)]
    # new coordinates: position j <- rep[j], position n2+j <- a(rep[j])
    newpos = {}
    for j in range(n2):
        newpos[rep[j]] = j; newpos[a[rep[j]]] = n2 + j
    perm = [newpos[i] for i in range(n)]
    Cn = [apply_perm_vec(perm, v) for v in C]
    # check a, b act as standard in new coordinates
    pa = perm_a(n2)
    pb = [beta[i] if i < n2 else beta[i - n2] + n2 for i in range(n)]
    assert is_aut(pa, Cn, n) and is_aut(pb, Cn, n)
    lo = (1 << n2) - 1
    Ybasis = echelon([(v & lo) ^ (v >> n2) for v in Cn])
    fixed = [v for v in Cn]  # fixed code check
    assert len(Ybasis) == 12, len(Ybasis)
    # Y equals contracted fixed code: (y|y) in C for y in Y
    SC = Span(Cn)
    assert all(SC.contains(y | (y << n2)) for y in Ybasis)
    I = Instance(Ybasis, beta, 12, "qr48_" + tag)
    o, west, nf = best_order(I)
    path = HERE + "/inst48_%s.txt" % tag
    export(I, path)
    t0 = time.time()
    out = subprocess.run([HERE + "/search", path], capture_output=True, text=True).stdout
    secs = time.time() - t0
    sols = [tuple(int(t) for t in line.split()[1:]) for line in out.splitlines() if line.startswith("SOL")]
    stats = [line for line in out.splitlines() if line.startswith("STATS") or line.startswith("LEVEL")]
    # QR48's own B, reduced into the slice
    G = [[0] * I.k for _ in range(I.k)]
    for i in range(I.k):
        # find c in Cn with u+v = w_i
        # solve: c = sum of Cn rows with (u+v) = w_i
        target = I.w[i]
        img = [((v & lo) ^ (v >> n2), v) for v in Cn]
        # elimination
        piv = []
        for yv, cv in img:
            for p, py, pc in piv:
                if (yv >> p) & 1:
                    yv ^= py; cv ^= pc
            if yv:
                piv.append((yv.bit_length() - 1, yv, cv))
        t = target; c = 0
        for p, py, pc in piv:
            if (t >> p) & 1:
                t ^= py; c ^= pc
        assert t == 0
        z = c & lo
        for l in range(I.k):
            G[i][l] = dot(z, I.w[l])
    # check symmetric, beta-invariant, diag constraint
    k = I.k
    assert all(G[i][l] == G[l][i] for i in range(k) for l in range(k))
    vec = 0
    for i in range(k):
        for l in range(i, k):
            if G[i][l]:
                vec |= 1 << I.idx[(i, l)]
    # express vec - part in span(H) + span(gauge)
    diff = vec ^ I.part
    # rebuild gauge echelon + H: reduce by pivots in same way
    # simple approach: solve linear system over the combined basis
    from structure import solve_affine
    basis = I.H + gauge_vectors(I)
    eqs = []
    for bit in range(I.nent):
        m = 0
        for j, h in enumerate(basis):
            if (h >> bit) & 1:
                m |= 1 << j
        eqs.append((m, (diff >> bit) & 1))
    sol = solve_affine(eqs, len(basis))
    assert sol is not None, "QR48 B not in parametrised family!"
    xq = tuple((sol[0] >> s) & 1 for s in range(I.N))
    found = xq in set(sols)
    # verify all solutions
    nver = 0
    dists = []
    for x in sols:
        Gx = gram_from_x(I, x)
        rows = build_code(I, Gx)
        info = verify_code(I, rows, 12)
        ok = (info['rank'] == 24 and info['selforth'] and info['doubly_even'] and info['inv_a'] and info['inv_b'] and info['d'] == 12)
        assert ok, info
        dists.append(info['d'])
        nver += 1
    res = dict(tag=tag, N=I.N, k_t=I.k_t, ncons=len(I.cons), nsol=len(sols), qr48_found=found,
               verified=nver, all_d12=all(d == 12 for d in dists), secs=round(secs, 2), log2est=round(west, 2),
               stats=stats)
    print(json.dumps(res), flush=True)
    return res

def gauge_vectors(I):
    k = I.k
    orbs = []
    seenp = set()
    for i in range(I.n2):
        if i not in seenp:
            orbs.append((i, I.beta[i])); seenp |= {i, I.beta[i]}
    def DT(T):
        m = 0
        for i in range(k):
            for l in range(i, k):
                if popcount(I.w[i] & I.w[l] & T) & 1:
                    m |= 1 << I.idx[(i, l)]
        return m
    g = [DT((1 << i) | (1 << j)) for (i, j) in orbs]
    tr = 0
    for (i, j) in orbs:
        tr |= 1 << i
    g.append(DT(tr))
    return g

if __name__ == '__main__':
    main()
