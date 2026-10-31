"""QR80 positive control (distance 16) with prefix-restricted exhaustive subtree searches."""
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
from control80 import qr80, min_weight_upto12, psl_gens, systematic
from structure import solve_affine

ENGINE = HERE + "/search_v4"

def setup(C, a, b, tag):
    n = 80; n2 = 40
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
            rep[j] = pairs[j][0]
            jb = pair_of[b[rep[j]]]
            rep[jb] = b[rep[j]]
    beta = [pair_of[b[rep[j]]] for j in range(n2)]
    newpos = {}
    for j in range(n2):
        newpos[rep[j]] = j; newpos[a[rep[j]]] = n2 + j
    perm = [newpos[i] for i in range(n)]
    Cn = [apply_perm_vec(perm, v) for v in C]
    assert is_aut(perm_a(n2), Cn, n)
    lo = (1 << n2) - 1
    Ybasis = echelon([(v & lo) ^ (v >> n2) for v in Cn])
    assert len(Ybasis) == 20
    I = Instance(Ybasis, beta, 16, "qr80_" + tag)
    best_order(I)
    path = HERE + "/inst80_%s.txt" % tag
    vstart = export(I, path)
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
    vec = 0
    for i in range(k):
        for l in range(i, k):
            if G[i][l]:
                vec |= 1 << I.idx[(i, l)]
    diff = vec ^ I.part
    basis = I.H + gauge_vectors(I)
    eqs = []
    for bit in range(I.nent):
        m = 0
        for j, h in enumerate(basis):
            if (h >> bit) & 1:
                m |= 1 << j
        eqs.append((m, (diff >> bit) & 1))
    sol = solve_affine(eqs, len(basis))
    assert sol is not None, "QR80 B not in parametrised family"
    xq = tuple((sol[0] >> s) & 1 for s in range(I.N))
    # sanity: the slice element xq gives a code gauge-equivalent to Cn: same weight structure; check it is
    # doubly-even self-dual invariant and has no words of weight <= 12
    rows = build_code(I, gram_from_x(I, xq))
    info = verify_code(I, rows, 16, full_distance=False)
    assert info['rank'] == 40 and info['selforth'] and info['doubly_even'] and info['inv_a'] and info['inv_b']
    assert not min_weight_upto12(echelon(rows), 80)
    return I, path, vstart, xq

def run_prefix(I, path, vstart, xq, L, timeout):
    P = vstart[L]
    env = dict(os.environ)
    env["V4_PREFIX"] = "".join(str(b) for b in xq[:P])
    t0 = time.time()
    try:
        out = subprocess.run([ENGINE, path], capture_output=True, text=True, env=env, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        return dict(L=L, P=P, timeout=True)
    secs = time.time() - t0
    sols = [tuple(int(t) for t in line.split()[1:]) for line in out.splitlines() if line.startswith("SOL")]
    stats = [line for line in out.splitlines() if line.startswith("STATS") or line.startswith("LEVEL")]
    nver = 0
    for x in sols:
        rows = build_code(I, gram_from_x(I, x))
        info = verify_code(I, rows, 16, full_distance=False)
        assert info['rank'] == 40 and info['selforth'] and info['doubly_even'] and info['inv_a'] and info['inv_b']
        assert not min_weight_upto12(echelon(rows), 80), "solution with small words!"
        nver += 1
    return dict(L=L, P=P, nfree=I.N - P, nsol=len(sols), qr80_found=(xq in set(sols)), verified=nver,
                secs=round(secs, 1), stats=stats)

def main():
    C = qr80()
    gens = psl_gens()
    for g in gens:
        assert is_aut(list(g), C, 80)
    a = gens[2]
    e = tuple(range(80))
    G = closure(gens, 80)
    bs = [g for g in G if g != e and g != a and compose(g, g) == e and compose(a, g) == compose(g, a)]
    # V4 class representatives
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
    for b in sorted(bs):
        V = frozenset([a, b, compose(a, b)])
        if V in covered:
            continue
        covered |= orbit(V)
        reps.append(b)
    print("V4 classes:", len(reps), flush=True)
    results = []
    for ci, b in enumerate(reps):
        I, path, vstart, xq = setup(C, a, b, "c%d" % ci)
        print("class", ci, "N", I.N, "k_t", I.k_t, "vstart", vstart, flush=True)
        for L in (14, 12, 11, 10, 9):
            r = run_prefix(I, path, vstart, xq, L, timeout=1500)
            r['cls'] = ci
            print(json.dumps({kk: vv for kk, vv in r.items() if kk != 'stats'}), flush=True)
            results.append(r)
            if r.get('timeout'):
                break
    json.dump(results, open(HERE + '/control80_results.json', 'w'), indent=1)
    print("CONTROL80 DONE")

if __name__ == '__main__':
    main()
