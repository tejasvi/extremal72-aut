"""Check of the 18th gauge direction (transversal swap s_T0, which conjugates b to ab):
 A) length-72 instances: orbit-swap deltas have rank 17 (they sum to 0); D_T0 is independent (rank 18);
    s_T0(C_B) = C_{B+D_T0} as codes, it is invariant under a and b, and s_T0 b s_T0 = ab.
 B) QR48 control with the 17-dimensional gauge only: twice as many slice solutions, mapping 2-to-1 onto the
    solutions of the 18-dimensional slice."""
import sys, json, random, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from instance import Instance
from export import export, gram_from_x, build_code, perm_a, perm_b
from autgroup import apply_perm_vec, is_aut
from control48 import gauge_vectors, qr48
from fpfclasses import closure, compose, inverse
from order import best_order
from structure import solve_affine
D = HERE
rng = random.Random(2026)

def partA(name):
    meta = json.load(open(D + '/inst2/%s.json' % name))
    codes = json.load(open(D + '/data/codes41.json'))
    I = Instance(codes[meta['code'] - 1]['basis'], meta['beta'], 16)
    I.set_order(meta['order'])
    g = gauge_vectors(I)            # 18 orbit deltas, then the transversal delta
    orb, trans = g[:-1], g[-1]
    s = 0
    for v in orb:
        s ^= v
    r17, r18 = rank(orb), rank(orb + [trans])
    n2 = I.n2
    # transversal T0 used by gauge_vectors: first element of each beta-orbit in increasing order
    T0 = 0; seen = set()
    for i in range(n2):
        if i not in seen:
            T0 |= 1 << i; seen |= {i, I.beta[i]}
    sT = [(i + n2 if (T0 >> i) & 1 else i) if i < n2 else ((i - n2) if (T0 >> (i - n2)) & 1 else i) for i in range(2 * n2)]
    pa, pb = perm_a(n2), perm_b(I)
    conj_ok = compose(compose(tuple(sT), tuple(pb)), tuple(sT)) == compose(tuple(pa), tuple(pb))
    ok_codes = True
    for trial in range(3):
        x = [rng.randrange(2) for _ in range(I.N)]
        G = gram_from_x(I, x)
        rows = build_code(I, G)
        G2 = [[G[i][l] ^ (popcount(I.w[i] & I.w[l] & T0) & 1) for l in range(I.k)] for i in range(I.k)]
        rows2 = build_code(I, G2)
        perm_rows = [apply_perm_vec(sT, r) for r in rows]
        S1, S2 = Span(perm_rows), Span(rows2)
        same = all(S2.contains(r) for r in perm_rows) and all(S1.contains(r) for r in rows2)
        inv = is_aut(pa, rows2, 2 * n2) and is_aut(pb, rows2, 2 * n2)
        de = all(popcount(r) % 4 == 0 for r in rows2) and all(dot(p, q) == 0 for p in rows2 for q in rows2)
        ok_codes &= same and inv and de
    print(json.dumps(dict(instance=name, sum_of_18_orbit_deltas_is_zero=(s == 0), rank_orbit_deltas=r17,
                          rank_with_transversal=r18, conj_sT_b_sT_equals_ab=conj_ok,
                          sT_of_C_B_equals_C_B_plus_DT0_invariant_doubly_even_selfdual=ok_codes)), flush=True)

def run(path):
    out = subprocess.run([D + '/search_v4', path], capture_output=True, text=True).stdout
    return [tuple(int(t) for t in l.split()[1:]) for l in out.splitlines() if l.startswith('SOL')]

def partB():
    C = qr48()
    p = 47; inf = 47
    def mk(f):
        return tuple(f(x) for x in range(48))
    sqs = sorted(set((x * x) % p for x in range(1, p)))
    gsq = next(g for g in sqs if len(set(pow(g, e, p) for e in range(1, 24))) == 23)
    gens = [mk(lambda x: inf if x == inf else (x + 1) % p), mk(lambda x: inf if x == inf else (gsq * x) % p),
            mk(lambda x: 0 if x == inf else (inf if x == 0 else (-pow(x, p - 2, p)) % p))]
    G = closure(gens, 48)
    e = tuple(range(48))
    invs = sorted(g for g in G if g != e and compose(g, g) == e)
    results = []
    # one V4 from each conjugacy class (same selection as control48: first found class reps)
    V4s = {}
    for a in invs:
        for b in invs:
            if a < b and compose(a, b) == compose(b, a):
                V4s.setdefault(frozenset([a, b, compose(a, b)]), (a, b))
    rem = set(V4s); reps = []
    while rem:
        V = min(rem, key=lambda X: sorted(X)); orb = {V}; fr = [V]
        while fr:
            nf = []
            for X in fr:
                for s_ in gens:
                    si = inverse(s_)
                    Yv = frozenset(compose(compose(si, x), s_) for x in X)
                    if Yv not in orb:
                        orb.add(Yv); nf.append(Yv)
            fr = nf
        rem -= orb; reps.append(V)
    for ci, V in enumerate(reps):
        a = sorted(V)[0]; b = sorted(V)[1]
        n = 48; n2 = 24
        pairs = []; seen = set()
        for i in range(n):
            if i not in seen:
                pairs.append((i, a[i])); seen |= {i, a[i]}
        pair_of = {}
        for j, (x, y) in enumerate(pairs):
            pair_of[x] = j; pair_of[y] = j
        rep = [None] * n2
        for j in range(n2):
            if rep[j] is None:
                rep[j] = pairs[j][0]; rep[pair_of[b[rep[j]]]] = b[rep[j]]
        beta = [pair_of[b[rep[j]]] for j in range(n2)]
        newpos = {}
        for j in range(n2):
            newpos[rep[j]] = j; newpos[a[rep[j]]] = n2 + j
        Cn = [apply_perm_vec([newpos[i] for i in range(n)], v) for v in C]
        lo = (1 << n2) - 1
        Yb = echelon([(v & lo) ^ (v >> n2) for v in Cn])
        I18 = Instance(Yb, beta, 12)
        best_order(I18)
        order = list(I18.w)
        I18.set_order(order)
        export(I18, '/tmp/v4i_g18.txt'); s18 = run('/tmp/v4i_g18.txt')
        I17 = Instance(Yb, beta, 12)
        I17.set_order(order, use_transversal=False)
        export(I17, '/tmp/v4i_g17.txt'); s17 = run('/tmp/v4i_g17.txt')
        basis18 = I18.H + gauge_vectors(I18)
        img = {}
        for x in s17:
            v = I17.part
            for sidx, bit in enumerate(x):
                if bit:
                    v ^= I17.H[sidx]
            diff = v ^ I18.part
            eqs = []
            for bit in range(I18.nent):
                m = 0
                for j, h in enumerate(basis18):
                    if (h >> bit) & 1:
                        m |= 1 << j
                eqs.append((m, (diff >> bit) & 1))
            sol = solve_affine(eqs, len(basis18))
            y = tuple((sol[0] >> sidx) & 1 for sidx in range(I18.N))
            img[y] = img.get(y, 0) + 1
        two_to_one = set(img) == set(s18) and all(c == 2 for c in img.values())
        results.append(dict(v4_class=ci, N18=I18.N, N17=I17.N, nsol_gauge18=len(s18), nsol_gauge17=len(s17),
                            map_17_to_18_is_exactly_2_to_1_onto=two_to_one))
        print(json.dumps(results[-1]), flush=True)

if __name__ == '__main__':
    for nm in ['i72_c01_b0', 'i72_c04_b5', 'i72_c24_b4', 'i72_c22_b2']:
        partA(nm)
    partB()
