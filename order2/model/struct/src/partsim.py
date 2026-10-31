"""Monte-Carlo potential of bit-granular LTS tests (component 0 only).  Random symmetric forms M on Y (flag
coordinates); for each level t a node survives the current engine's test iff K0(B) <= K0(B^g) for every g whose
transported k0-syndrome is fully determined at t; the bit-granular test also prunes when a g has a determined
leading-bit prefix (MSB first, the engine's integer order) that is already smaller.  Bit j of the transported
syndrome is B(g k0, g c_j); it is determined at t iff min(L(g k0), L(g c_j), L(g k0 + g c_j)) <= t (the criterion of
partbits.py, conservative).  Orders: 'ub' = the instance's syndrome basis; 'greedy' = a basis of Y_k0 chosen MSB
first to lie in as many determined subspaces as possible at level TSTAR.
Usage: partsim.py CI PKGDIR K0 LEVELS NSAMP [TSTAR]"""
import sys, os, pickle, random
import numpy as np
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst
from partbits_lib import closure, ap

ci = int(sys.argv[1]); pk = sys.argv[2]; k0 = int(sys.argv[3])
levels = [int(x) for x in sys.argv[4].split(',')]; nsamp = int(sys.argv[5])
tstar = int(sys.argv[6]) if len(sys.argv) > 6 else levels[len(levels) // 2]
flag = [int(x) for x in open(f'{pk}/flag.txt').read().split()[1:]]
meta = [list(map(int, l.split())) for l in open(f'{pk}/inst.txt.meta')]
ub = [row[1:] for row in meta if row[0] == k0][0]; m0 = len(ub)
perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
G = closure(perms)
n = len(flag); words = np.zeros(1 << n, dtype=np.int64); L = np.full(1 << n, -1, dtype=np.int64)
for i, v in enumerate(flag):
    words[1 << i: 1 << (i + 1)] = words[0: 1 << i] ^ v; L[1 << i: 1 << (i + 1)] = i
coord = dict(zip(words.tolist(), range(1 << n))); Lw = dict(zip(words.tolist(), L.tolist()))
Yk = [int(x) for x in words[(words & k0) == 0]]


def span_ok(basis, c):
    return True


def det_level(g, c):
    u = ap(g, k0); gc = ap(g, c)
    return min(Lw[u], Lw[gc], Lw[u ^ gc])


# greedy basis of Y_k0 (MSB first) for level tstar, among g not fully determined at tstar
partial_g = [g for g in G if not (Lw[ap(g, k0)] <= tstar or all(det_level(g, c) <= tstar for c in ub))]
def reduce_vec(piv, v):
    for b in sorted(piv, reverse=True):
        if v >> b & 1: v ^= piv[b]
    return v
chosen = []; piv = {}; alive = list(partial_g)
# coordinates of Y_k0 words relative to ub basis are not needed: any basis of Y_k0 defines a valid order
cand = Yk[1:]
while len(chosen) < m0:
    best = None; bscore = -1
    for c in cand:
        r = reduce_vec(piv, c)
        if r == 0: continue
        sc = sum(1 for g in alive if det_level(g, c) <= tstar)
        if sc > bscore: bscore, best, bred = sc, c, r
    chosen.append(best); piv[bred.bit_length() - 1] = bred
    alive = [g for g in alive if det_level(g, best) <= tstar]
order_greedy = chosen[::-1]      # bit j = chosen[m0-1-j]: MSB (j = m0-1) = first chosen
print(f"Y{ci} |G|={len(G)} k0={k0} m0={m0} partial g at t*={tstar}: {len(partial_g)}; greedy prefix survivors per "
      f"depth computed on those g")
orders = {'ub': ub, 'greedy': order_greedy}
# precompute per order, per g: transported vectors g c_j and their determination levels
pre = {}
for name, basis in orders.items():
    rows = []
    for g in G:
        u = ap(g, k0)
        gc = [ap(g, c) for c in basis]
        dl = [min(Lw[u], Lw[x], Lw[u ^ x]) for x in gc]
        rows.append((u, gc, dl))
    pre[name] = rows
rng = np.random.default_rng(12345)


def form_val(M, x, y):
    cx = coord[x]; cy = coord[y]; my = 0
    j = 0
    while cy:
        if cy & 1: my ^= M[j]
        cy >>= 1; j += 1
    return bin(cx & my).count('1') & 1


res = {name: {t: [0, 0] for t in levels} for name in orders}
for s in range(nsamp):
    A = rng.integers(0, 2, size=(n, n)); A = np.triu(A); A = A ^ np.triu(A, 1).T
    M = [int(''.join(str(int(b)) for b in A[:, j][::-1]), 2) for j in range(n)]   # column j as int over rows
    for name, basis in orders.items():
        rows = pre[name]
        K0 = sum(form_val(M, k0, c) << j for j, c in enumerate(basis))
        vals = [[form_val(M, u, x) for x in gc] for (u, gc, dl) in rows]
        for t in levels:
            if Lw[k0] > t: continue
            full_ok = True; part_ok = True
            for (u, gc, dl), bits in zip(rows, vals):
                if max(dl) <= t:
                    Kg = sum(b << j for j, b in enumerate(bits))
                    if Kg < K0: full_ok = False; part_ok = False; break
                else:
                    for j in range(m0 - 1, -1, -1):        # MSB first
                        if dl[j] > t: break
                        kb = K0 >> j & 1
                        if bits[j] != kb:
                            if bits[j] < kb: part_ok = False
                            break
            res[name][t][0] += full_ok; res[name][t][1] += part_ok
for name in orders:
    print(f" order {name}: " + '  '.join(f"t{t}: full 1/{nsamp / max(1, res[name][t][0]):.1f} +bits 1/{nsamp / max(1, res[name][t][1]):.1f}" for t in levels))
