"""Independent numpy re-computation of search levels 2-4 for given nodes (validates search.c).
Uses only py/gf.py (spec-level definitions).  Conventions shared with search.c by design (they define
the canonical form): class codes 0/1/2/3 = zero/norm 1/norm W/norm W2, pattern index sum cls_i<<2i,
packed value sum u_i<<4i, orbit order (size desc, then min pattern index), orbit rep = least element
of each class, positions filled in order 0,1,3,2,4,5,6.
usage: validate.py THR K0 dumpfile node1hex [maxnodes2 maxnodes3]"""
import sys, itertools, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gf import *

THR = int(sys.argv[1]); K0 = int(sys.argv[2]); DUMP = sys.argv[3]; NODE1 = int(sys.argv[4], 16)
MAX2 = int(sys.argv[5]) if len(sys.argv) > 5 else 3
MAX3 = int(sys.argv[6]) if len(sys.argv) > 6 else 3
POS = [0, 1, 3, 2, 4, 5, 6]
MULn = np.array(MUL, dtype=np.uint8); CONJn = np.array(CONJ, dtype=np.uint8)
CLSl = [0 if y == 0 else (1 if NORM[y] == 1 else (2 if NORM[y] == W else 3)) for y in range(16)]
CLSn = np.array(CLSl, dtype=np.int64); WTn = np.array(WT, dtype=np.int64)
Smat = np.array([[1 if i in S else 0 for i in range(7)] for S, x in P], dtype=np.int64)   # 16 x 7
Xv = np.array([x for S, x in P], dtype=np.int64); Ssz = Smat.sum(1)

def Mw(Wt):            # weights (N,7) -> M (N,)
    cost = Xv[None, :] + Wt.sum(1)[:, None] + 5 * Ssz[None, :] - 2 * (Wt @ Smat.T)
    return cost.min(1)
def Mvecs(V):          # vectors (N,7) uint8
    return Mw(WTn[V])
def packed(V):         # (N,7) -> int
    return (V.astype(np.int64) << (4 * np.arange(7))[None, :]).sum(1)
def herm1(u, v):
    s = 0
    for a, b in zip(u, v): s ^= MUL[a][CONJ[b]]
    return s

# ---- R, orbits, keys ----
GL = [p for p in itertools.permutations(range(7)) if all(frozenset(p[i] for i in L) in set(LINES) for L in LINES)]
assert len(GL) == 168
def pat_index(cl): return sum(c << (2 * i) for i, c in enumerate(cl))
def inR_pattern(cl):
    s = 0
    for c in cl: s ^= [0, 1, W, W2][c]
    if s != 1: return False
    for cc in range(1, 16):
        w = []
        for c in cl:
            y = [0, 1, 5, 3][c]          # any element of the class
            w.append(WT[MUL[cc][y]])
        if M_of_weights(w) < THR - WT[cc]: return False
    return True
Rpats = [cl for cl in itertools.product(range(4), repeat=7) if inR_pattern(cl)]
Rset = set(Rpats)
orb_of = {}
orbits = []
for cl in sorted(Rpats, key=pat_index):
    if cl in orb_of: continue
    orb = set()
    for g in GL:
        for f in range(2):
            q = [0] * 7
            for i in range(7): q[g[i]] = cl[i]
            if f: q = [c if c < 2 else c ^ 1 for c in q]
            orb.add(tuple(q))
    nnz = sum(1 for c in cl if c)
    orbits.append((len(orb) * 5 ** nnz, min(pat_index(q) for q in orb), orb))
    for q in orb: orb_of[q] = len(orbits) - 1
order = sorted(range(len(orbits)), key=lambda k: (-orbits[k][0], orbits[k][1]))
keymap = {}
for newk, k in enumerate(order):
    for q in orbits[k][2]: keymap[q] = newk
print("python: |R patterns| =", len(Rpats), "orbits =", len(orbits))
def key_of(u): return keymap.get(tuple(CLSl[y] for y in u), -1)
def rep_vector(k):
    p = orbits[order[k]][1]
    cl = [(p >> (2 * i)) & 3 for i in range(7)]
    return [[0, 1, 5, 3][c] for c in cl]
r = rep_vector(K0)
print("python rep r =", ''.join('%x' % y for y in reversed(r)))
keytab = np.full(16384, -1, dtype=np.int64)
for q, k in keymap.items(): keytab[pat_index(q)] = k
def keys(V): return keytab[(CLSn[V] << (2 * np.arange(7))[None, :]).sum(1)]

# allowed partial column patterns (EXT): restriction to known positions of R-patterns with key >= K0
def ext_set(known):
    return set(tuple(q[i] for i in known) for q, k in keymap.items() if k >= K0)

# ---- stabiliser of r and key2 (brute force over D on zero positions and zeta) ----
def frobv(u, f):
    for _ in range(f): u = [SQR for SQR in (MUL[y][y] for y in u)]
    return u
stab = []
Z = [i for i in range(7) if r[i] == 0]
for g in GL:
    for f in range(4):
        w = frobv(list(r), f)
        wp = [0] * 7
        for i in range(7): wp[g[i]] = w[i]
        if [CLSl[y] for y in wp] != [CLSl[y] for y in r]: continue
        for dz in itertools.product(MU5, repeat=len(Z)):
            D = [MUL[r[i]][INV[wp[i]]] if r[i] else 1 for i in range(7)]
            for t, i in enumerate(Z): D[i] = dz[t]
            stab.append((g, f, D))
print("python |Stab(r)| incl. zero-position scalings =", len(stab))
def gapply(e, u):
    g, f, D = e
    w = frobv(list(u), f)
    out = [0] * 7
    for i in range(7): out[g[i]] = MUL[D[g[i]]][w[i]]
    return out
for e in stab: assert gapply(e, r) == list(r)
def pk(u): return sum(y << (4 * i) for i, y in enumerate(u))
def minrep(u): return min(pk([MUL[z][y] for y in u]) for z in MU5)
def key2(u): return min(minrep(gapply(e, u)) for e in stab)
def unpk(v): return [(v >> (4 * i)) & 15 for i in range(7)]

# ---- linear algebra: orthogonal complement ----
def complement(rows):
    # solve sum_i u_i conj(row_i) = 0 for all rows; Gaussian elimination over GF(16)
    A = [[CONJ[y] for y in row] for row in rows]
    piv = []; A = [list(a) for a in A]; rk = 0
    for col in range(7):
        pr = next((i for i in range(rk, len(A)) if A[i][col]), None)
        if pr is None: continue
        A[rk], A[pr] = A[pr], A[rk]
        inv = INV[A[rk][col]]; A[rk] = [MUL[inv][y] for y in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][col]:
                f = A[i][col]; A[i] = [A[i][j] ^ MUL[f][A[rk][j]] for j in range(7)]
        piv.append(col); rk += 1
    free = [c for c in range(7) if c not in piv]
    basis = []
    for fc in free:
        u = [0] * 7; u[fc] = 1
        for i, pc in enumerate(piv): u[pc] = A[i][fc]       # char 2: -x = x
        basis.append(u)
    for b in basis:
        for row in rows: assert herm1(b, row) == 0
    return basis
def span(basis):
    n = len(basis); V = np.zeros((16 ** n, 7), dtype=np.uint8)
    idx = np.arange(16 ** n)
    for t, b in enumerate(basis):
        coef = (idx >> (4 * t)) & 15
        V ^= MULn[coef[:, None], np.array(b, dtype=np.uint8)[None, :]]
    return V

# ---- (*) on all a supported on POS[0..d] with a_{POS[d]} != 0 (no symmetry reduction) ----
def prefix_tables(rows, d):
    n = 16 ** d; idx = np.arange(n)
    V0 = np.zeros((n, 7), dtype=np.uint8); Wa = np.zeros((n, 7), dtype=np.int64)
    for j in range(d):
        coef = (idx >> (4 * j)) & 15
        V0 ^= MULn[coef[:, None], np.array(rows[j], dtype=np.uint8)[None, :]]
        Wa[:, POS[j]] = WTn[coef]
    return V0, Wa
def star_ok(V0, Wa, d, u):
    u = np.array(u, dtype=np.uint8)
    for ad in range(1, 16):
        Wad = Wa.copy(); Wad[:, POS[d]] = WT[ad]
        V = V0 ^ MULn[ad][u][None, :]
        if np.any(Mw(Wad) + Mvecs(V) < THR): return False
    return True

def candidates(rows, d, k2min):
    """all rows for position POS[d] given rows at POS[0..d-1], with every canonical-form condition"""
    basis = complement(rows)
    V = span(basis)
    nrm = np.zeros(len(V), dtype=np.uint8)
    for i in range(7): nrm ^= MULn[V[:, i], CONJn[V[:, i]]]
    V = V[nrm == 1]
    kk = keys(V); V = V[kk >= K0]
    known = [POS[j] for j in range(d + 1)]
    E = ext_set(known)
    colcls_prev = [[CLSl[rows[j][c]] for j in range(d)] for c in range(7)]
    keep = []
    for u in V:
        ul = [int(y) for y in u]
        if minrep(ul) != pk(ul): continue
        if not all(tuple(colcls_prev[c] + [CLSl[ul[c]]]) in E for c in range(7)): continue
        keep.append(ul)
    V0, Wa = prefix_tables(rows, d)
    out = []
    for ul in keep:
        if key2(ul) < k2min: continue
        if star_ok(V0, Wa, d, ul): out.append(ul)
    return out, len(V)

# ---- read C dump ----
dump = {}
for line in open(DUMP):
    f = line.split()
    if f[0] != 'NODE': continue
    d = int(f[1][2:]); rows = tuple(int(x, 16) for x in f[2:])
    dump.setdefault(d, set()).add(rows)
rr = pk(r); c = NODE1
assert key2(unpk(c)) == c, "node1 not canonical"
rows01 = [r, unpk(c)]
# depth 2 (position 3)
c2, nunit = candidates(rows01, 2, c)
py2 = set((rr, c, pk(u)) for u in c2)
cd2 = set(t for t in dump.get(2, set()) if t[0] == rr and t[1] == c)
print("depth 2: python %d nodes, C %d nodes, equal = %s" % (len(py2), len(cd2), py2 == cd2))
# depth 3 (position 2) for a few depth-2 nodes
for t in sorted(py2)[:MAX2]:
    rows = [unpk(x) for x in t]
    c3, _ = candidates(rows, 3, c)
    py3 = set(t + (pk(u),) for u in c3)
    cd3 = set(s for s in dump.get(3, set()) if s[:3] == t)
    print("  depth 3 under %s: python %d, C %d, equal = %s" % (' '.join('%07x' % x for x in t), len(py3), len(cd3), py3 == cd3))
    for s in sorted(py3)[:MAX3]:
        rows4 = [unpk(x) for x in s]
        k2min = max(c, key2(rows4[3]))      # (C5)
        c4, _ = candidates(rows4, 4, k2min)
        c4raw, _ = candidates(rows4, 4, 0)
        print("    depth 4 under ...%07x: python %d nodes (%d ignoring key2 bounds)" % (s[3], len(c4), len(c4raw)))
