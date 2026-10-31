"""Rigorous proof that every symmetric form B on the Golay code G24 with B(y,y) = |y|/2 + B(y,1) has an odd number
of octads y with s_y(B) = 0 (s_y = B(y,.) restricted to G_y = {u in G : u & y = 0}).
Hence no doubly-even self-dual [48,24,12] code has a fpf involution with contracted code G24.
Method: variables = free Gram entries x (basis g_0 = 1, g_1..g_11): x = (M_00, M_0j (j>=1), M_ij (1<=i<j)), 67 bits;
diagonal M_ii = |g_i|/2 + M_i0 (i >= 1).  s_y(B) is affine-linear in x, so f(x) = #{y : s_y = 0} mod 2 is a
polynomial of degree <= 4 (each indicator is a product of 4 affine forms; s_y(1+y) = 0 automatically).
A nonzero F2-polynomial of degree <= d has a nonzero value at some point of Hamming weight <= d (minimal monomial),
so f == 1 iff f(x) = 1 for all x of weight <= 4 (816,664 points)."""
import sys
from itertools import combinations
import numpy as np
sys.path.insert(0, '<HOME>/c72/c2opt/math')
from mc import span_np, pc, reduce_basis
from golay import golay24
from lowcount import basis_with_ones

n2 = 24
basis = basis_with_ones(golay24(), n2)
k = len(basis)
assert k == 12 and basis[0] == (1 << n2) - 1
Y = span_np(basis)
wy = np.bitwise_count(Y)
assert sorted(set(int(w) for w in wy.tolist())) == [0, 8, 12, 16, 24]
# coordinates
piv = {}
for i, g in enumerate(basis):
    v, c = g, 1 << i
    for b in sorted(piv, reverse=True):
        if (v >> b) & 1:
            v ^= piv[b][0]; c ^= piv[b][1]
    piv[v.bit_length() - 1] = (v, c)
def coords(w):
    c = 0
    for b in sorted(piv, reverse=True):
        if (w >> b) & 1:
            w ^= piv[b][0]; c ^= piv[b][1]
    assert w == 0
    return c
octs = [int(v) for v in Y[wy == 8].tolist()]
assert len(octs) == 759
# per octad: basis of G_y modulo 1+y (4 vectors)
U = []
for y in octs:
    sh = [int(u) for u in Y[(Y & np.uint64(y)) == 0].tolist()]
    assert len(sh) == 32
    comp = ((1 << n2) - 1) ^ y
    bas = list(reduce_basis([comp] + sh).values())
    assert len(bas) == 5
    # choose 4 vectors completing comp
    b4 = []
    cur = [comp]
    for u in sh:
        if len(reduce_basis(cur + [u])) > len(reduce_basis(cur)):
            cur.append(u); b4.append(u)
        if len(b4) == 4: break
    U.append(b4)
var = [(0, 0)] + [(0, j) for j in range(1, k)] + [(i, j) for i in range(1, k) for j in range(i + 1, k)]
assert len(var) == 67
def gram(xset):
    M = np.zeros((k, k), dtype=np.int64)
    for t in xset:
        i, j = var[t]
        M[i, j] ^= 1
        if i != j: M[j, i] ^= 1
    for i in range(1, k):
        M[i, i] = ((pc(basis[i]) // 2) + M[i, 0]) % 2
    return M
cy = np.array([[(coords(y) >> i) & 1 for i in range(k)] for y in octs], dtype=np.int64)        # 759 x 12
cu = np.array([[[(coords(u) >> i) & 1 for i in range(k)] for u in b4] for b4 in U], dtype=np.int64)  # 759 x 4 x 12
def synd(M):
    R = (cy @ M) % 2                       # B(y, g_i)
    s = np.einsum('yi,yki->yk', R, cu) % 2  # 759 x 4
    return (s * np.array([1, 2, 4, 8])).sum(axis=1)
# check diagonal condition implies s_y(1+y) = 0 (sanity on random forms)
rng = np.random.default_rng(1)
for _ in range(20):
    xs = [t for t in range(67) if rng.integers(2)]
    M = gram(xs)
    for idx, y in enumerate(octs[:50]):
        comp = ((1 << n2) - 1) ^ y
        c1 = np.array([(coords(y) >> i) & 1 for i in range(k)]); c2 = np.array([(coords(comp) >> i) & 1 for i in range(k)])
        assert (c1 @ M @ c2) % 2 == 0
base = synd(gram([]))
E = [synd(gram([t])) ^ base for t in range(67)]   # affine-linear: s(x) = base ^ xor_{t in x} E_t
# linearity check on random points
for _ in range(50):
    xs = [t for t in range(67) if rng.integers(2)]
    s = base.copy()
    for t in xs: s ^= E[t]
    assert np.array_equal(s, synd(gram(xs)))
E = np.array(E, dtype=np.uint8)
base = base.astype(np.uint8)
npts = 0; bad = 0
for d in range(0, 5):
    for S in combinations(range(67), d):
        s = base.copy()
        for t in S: s ^= E[t]
        z = int((s == 0).sum())
        npts += 1
        if z % 2 != 1:
            bad += 1
print('points checked', npts, 'with even count', bad)
print('THEOREM VERIFIED' if bad == 0 else 'FAILED')
