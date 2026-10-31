"""GF(16) = GF(2)[x]/(x^4+x^3+x^2+x+1), elements are 4-bit ints (bit k = coeff of x^k).
Hermitian form, weights, Fano side function M -- written from SPEC.md only."""
import itertools

MOD = 0b11111  # x^4+x^3+x^2+x+1

def mul_slow(a, b):
    r = 0
    for k in range(4):
        if (b >> k) & 1:
            r ^= a << k
    for k in (7, 6, 5, 4):          # reduce degree 7..4
        if (r >> k) & 1:
            r ^= MOD << (k - 4)
    return r

MUL = [[mul_slow(a, b) for b in range(16)] for a in range(16)]

def power(a, e):
    r = 1
    for _ in range(e):
        r = MUL[r][a]
    return r

CONJ = [power(y, 4) for y in range(16)]
NORM = [power(y, 5) for y in range(16)]
INV = [0] * 16
for a in range(1, 16):
    for b in range(1, 16):
        if MUL[a][b] == 1:
            INV[a] = b
GF4 = sorted(set(NORM))                      # {0,1,w,w^2} inside GF(16)
W = [y for y in GF4 if y not in (0, 1)][0]   # a fixed primitive cube root of unity
W2 = MUL[W][W]
MU5 = [y for y in range(1, 16) if NORM[y] == 1]

def wt(y):
    if y == 0:
        return 0
    return 4 if NORM[y] == 1 else 2

WT = [wt(y) for y in range(16)]

LINES = [frozenset(s) for s in ([0,1,3],[1,2,4],[2,3,5],[3,4,6],[4,5,0],[5,6,1],[6,0,2])]
ALL = frozenset(range(7))
P = [(frozenset(), 0)] + [(L, 1) for L in LINES] + [(ALL - L, 0) for L in LINES] + [(ALL, 1)]
assert len(P) == 16

def M_of_weights(w):
    best = None
    for S, x in P:
        val = 5 * len(S) + x + sum(w[i] for i in range(7) if i not in S) - sum(w[i] for i in S)
        if best is None or val < best:
            best = val
    return best

def M(v):
    return M_of_weights([WT[y] for y in v])

def herm(u, v):
    s = 0
    for a, b in zip(u, v):
        s ^= MUL[a][CONJ[b]]
    return s

def scal(c, v):
    return [MUL[c][y] for y in v]

def vecmat(a, U):
    out = [0] * len(U[0])
    for i, ai in enumerate(a):
        if ai:
            for j in range(len(out)):
                out[j] ^= MUL[ai][U[i][j]]
    return out
