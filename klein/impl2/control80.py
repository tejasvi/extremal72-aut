"""Second positive control (distance 16, same constraint types as at length 72):
extended QR code of length 80 (doubly-even self-dual [80,40,16]) with a freely acting Klein four-group
from PSL(2,79)."""
import sys, json, subprocess, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import apply_perm_vec, is_aut
from fpfclasses import closure, compose, inverse
from instance import Instance
from order import best_order
from export import *
from control48 import gauge_vectors
import numpy as np

P = 79
INF = 79

def qr80():
    p = P
    Q = sorted(set((x * x) % p for x in range(1, p)))
    NQ = [x for x in range(1, p) if x not in Q]
    for base in (Q, [0] + Q, NQ, [0] + NQ):
        rows = []
        for s in range(p):
            v = 0
            for q in base:
                v |= 1 << ((q + s) % p)
            if popcount(v) % 2:
                v |= 1 << p
            rows.append(v)
        B = echelon(rows)
        if len(B) == 40 and all(dot(x, y) == 0 for x in B for y in B) and all(popcount(x) % 4 == 0 for x in B):
            return B
    raise RuntimeError

def systematic(rows, cols, n):
    """Generator matrix in systematic form on coordinate set cols (must be an information set)."""
    rows = list(rows)
    out = []
    used = [False] * len(rows)
    for c in cols:
        sel = None
        for i, r in enumerate(rows):
            if not used[i] and (r >> c) & 1:
                sel = i; break
        if sel is None:
            return None
        used[sel] = True
        for i in range(len(rows)):
            if i != sel and (rows[i] >> c) & 1:
                rows[i] ^= rows[sel]
        out.append((c, sel))
    return [rows[sel] for c, sel in out]

def min_weight_upto12(B, n):
    """Exact test whether the doubly-even code span(B) (dim n/2) has a nonzero word of weight <= 12,
    using two disjoint information sets (Brouwer-Zimmermann with 2 sets)."""
    k = len(B)
    import random as _r
    rng = _r.Random(12345)
    perm = list(range(n))
    for attempt in range(1000):
        half1 = sorted(perm[:n // 2]); half2 = sorted(perm[n // 2:])
        if systematic(B, half1, n) is not None and systematic(B, half2, n) is not None:
            break
        rng.shuffle(perm)
    else:
        raise RuntimeError("no pair of disjoint information sets found")
    found = []
    from itertools import combinations
    for cols in (half1, half2):
        Sg = systematic(B, cols, n)
        assert Sg is not None, "not an information set"
        arr = np.array(Sg, dtype=object)
        # enumerate sums of <= 6 rows; weight of word >= number of rows (systematic part)
        rows_u = [np.uint64(r & ((1 << 64) - 1)) for r in Sg]
        rows_h = [np.uint64(r >> 64) for r in Sg]
        R_lo = np.array([r & ((1 << 64) - 1) for r in Sg], dtype=np.uint64)
        R_hi = np.array([r >> 64 for r in Sg], dtype=np.uint64)
        # iterate combinations level by level with numpy
        cur_lo = np.zeros(1, dtype=np.uint64); cur_hi = np.zeros(1, dtype=np.uint64)
        cur_last = np.array([-1])
        for depth in range(1, 7):
            new_lo = []; new_hi = []; new_last = []
            for j in range(k):
                mask = cur_last < j
                if not mask.any():
                    continue
                new_lo.append(cur_lo[mask] ^ R_lo[j]); new_hi.append(cur_hi[mask] ^ R_hi[j])
                new_last.append(np.full(int(mask.sum()), j))
            cur_lo = np.concatenate(new_lo); cur_hi = np.concatenate(new_hi); cur_last = np.concatenate(new_last)
            w = popcount_array(cur_lo) + popcount_array(cur_hi)
            if (w <= 12).any():
                found.append((depth, int((w <= 12).sum())))
    return found

def psl_gens():
    p = P
    def mk(f):
        return tuple(f(x) for x in range(p + 1))
    def tr(x):
        return INF if x == INF else (x + 1) % p
    sqs = sorted(set((x * x) % p for x in range(1, p)))
    g = next(s for s in sqs if len(set(pow(s, e, p) for e in range(1, (p - 1) // 2 + 1))) == (p - 1) // 2)
    def mul(x):
        return INF if x == INF else (g * x) % p
    def inv(x):
        if x == INF:
            return 0
        if x == 0:
            return INF
        return (-pow(x, p - 2, p)) % p
    return [mk(tr), mk(mul), mk(inv)]

def main():
    C = qr80()
    n = 80
    print("QR80 built: dim", len(C), flush=True)
    f = min_weight_upto12(C, n)
    print("words of weight <= 12 found:", f, flush=True)
    assert not f, "QR80 has small weight words?!"
    print("QR80 verified: doubly-even self-dual [80,40,16]", flush=True)
    gens = psl_gens()
    for g in gens:
        assert is_aut(list(g), C, n)
    print("PSL(2,79) generators verified as automorphisms", flush=True)
    a = gens[2]
    e = tuple(range(n))
    assert compose(a, a) == e and all(a[i] != i for i in range(n))
    G = closure(gens, n)
    print("group order", len(G), flush=True)
    assert len(G) == P * (P * P - 1) // 2
    bs = [g for g in G if g != e and g != a and compose(g, g) == e and compose(a, g) == compose(g, a)]
    V4s = []
    seen = set()
    for b in sorted(bs):
        V = frozenset([a, b, compose(a, b)])
        if V not in seen:
            seen.add(V); V4s.append((b, V))
    print("V4s containing a:", len(V4s), flush=True)
    # conjugacy class of each V4 in G (orbit under generators)
    def orbit(V):
        orb = {V}; fr = [V]
        while fr:
            nf = []
            for X in fr:
                for s in gens:
                    si = inverse(s)
                    Y = frozenset(compose(compose(si, x), s) for x in X)
                    if Y not in orb:
                        orb.add(Y); nf.append(Y)
            fr = nf
        return orb
    reps = []
    covered = set()
    for b, V in V4s:
        if V in covered:
            continue
        orb = orbit(V)
        covered |= orb
        reps.append((b, V, len(orb)))
    print("V4 classes represented:", [(len(reps))], [r[2] for r in reps], flush=True)
    results = []
    from control48 import run_control as rc48
    for ci, (b, V, sz) in enumerate(reps):
        results.append(run_control80(C, a, b, "c%d" % ci))
    json.dump(results, open(HERE + '/control80_results.json', 'w'), indent=1)
    print("CONTROL80 SUMMARY:", json.dumps([{k: v for k, v in r.items() if k != 'stats'} for r in results]))

def run_control80(C, a, b, tag):
    n = 80; n2 = 40
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
    newpos = {}
    for j in range(n2):
        newpos[rep[j]] = j; newpos[a[rep[j]]] = n2 + j
    perm = [newpos[i] for i in range(n)]
    Cn = [apply_perm_vec(perm, v) for v in C]
    pa = perm_a(n2)
    pb = [beta[i] if i < n2 else beta[i - n2] + n2 for i in range(n)]
    assert is_aut(pa, Cn, n) and is_aut(pb, Cn, n)
    lo = (1 << n2) - 1
    Ybasis = echelon([(v & lo) ^ (v >> n2) for v in Cn])
    assert len(Ybasis) == 20, len(Ybasis)
    SC = Span(Cn)
    assert all(SC.contains(y | (y << n2)) for y in Ybasis)
    I = Instance(Ybasis, beta, 16, "qr80_" + tag)
    print(tag, "Y: d =", I.dY, "constraints", len(I.cons), flush=True)
    o, west, nf = best_order(I)
    print(tag, "order chosen, N =", I.N, "k_t", I.k_t, "log2est %.1f" % west, flush=True)
    path = HERE + "/inst80_%s.txt" % tag
    export(I, path)
    # QR80's own B in the slice
    k = I.k
    img = [((v & lo) ^ (v >> n2), v) for v in Cn]
    piv = []
    for yv, cv in img:
        for p, py, pc in piv:
            if (yv >> p) & 1:
                yv ^= py; cv ^= pc
        if yv:
            piv.append((yv.bit_length() - 1, yv, cv))
    G = [[0] * k for _ in range(k)]
    for i in range(k):
        t = I.w[i]; c = 0
        for p, py, pc in piv:
            if (t >> p) & 1:
                t ^= py; c ^= pc
        assert t == 0
        z = c & lo
        for l in range(k):
            G[i][l] = dot(z, I.w[l])
    assert all(G[i][l] == G[l][i] for i in range(k) for l in range(k))
    vec = 0
    for i in range(k):
        for l in range(i, k):
            if G[i][l]:
                vec |= 1 << I.idx[(i, l)]
    diff = vec ^ I.part
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
    assert sol is not None, "QR80 B not in parametrised family!"
    xq = tuple((sol[0] >> s) & 1 for s in range(I.N))
    t0 = time.time()
    out = subprocess.run([HERE + "/search", path], capture_output=True, text=True).stdout
    secs = time.time() - t0
    sols = [tuple(int(t) for t in line.split()[1:]) for line in out.splitlines() if line.startswith("SOL")]
    stats = [line for line in out.splitlines() if line.startswith("STATS") or line.startswith("LEVEL")]
    found = xq in set(sols)
    # verify every solution: doubly-even, self-dual, invariant, no words of weight <= 12
    nver = 0
    for x in sols:
        Gx = gram_from_x(I, x)
        rows = build_code(I, Gx)
        info = verify_code(I, rows, 16, full_distance=False)
        ok = info['rank'] == 40 and info['selforth'] and info['doubly_even'] and info['inv_a'] and info['inv_b']
        assert ok, info
        f = min_weight_upto12(echelon(rows), 80) if systematic(rows, list(range(40)), 80) is not None and systematic(rows, list(range(40, 80)), 80) is not None else None
        assert f is not None, "halves not information sets"
        assert not f, "solution has small weight words!"
        nver += 1
    res = dict(tag=tag, N=I.N, k_t=I.k_t, ncons=len(I.cons), nsol=len(sols), qr80_found=found, verified=nver,
               secs=round(secs, 2), log2est=round(west, 2), stats=stats)
    print(json.dumps(res), flush=True)
    return res

if __name__ == '__main__':
    main()
