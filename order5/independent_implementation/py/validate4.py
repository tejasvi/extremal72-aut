"""For every depth-4 node dumped by search.c (rows at positions 0,1,3,2,4), check independently (numpy, gf.py only):
 (1) the 5 rows are orthonormal and (*) holds for every nonzero a supported on {0,1,2,3,4};
 (2) NO unit vector u in the orthogonal complement can be placed at position 5 such that (*) holds for every
     a supported on {0,1,2,3,4,5}  (no canonical-form restriction at all) -> the node has no completion.
usage: validate4.py THR dumpfile"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gf import *
THR = int(sys.argv[1])
POS = [0, 1, 3, 2, 4, 5, 6]
MULn = np.array(MUL, dtype=np.uint8); CONJn = np.array(CONJ, dtype=np.uint8); WTn = np.array(WT, dtype=np.int64)
Smat = np.array([[1 if i in S else 0 for i in range(7)] for S, x in P], dtype=np.int64)
Xv = np.array([x for S, x in P], dtype=np.int64); Ssz = Smat.sum(1)
def Mw(Wt):
    return (Xv[None, :] + Wt.sum(1)[:, None] + 5 * Ssz[None, :] - 2 * (Wt @ Smat.T)).min(1)
def unpk(v): return [(v >> (4 * i)) & 15 for i in range(7)]
def herm1(u, v):
    s = 0
    for a, b in zip(u, v): s ^= MUL[a][CONJ[b]]
    return s
def complement(rows):
    A = [[CONJ[y] for y in row] for row in rows]; piv = []; rk = 0
    for col in range(7):
        pr = next((i for i in range(rk, len(A)) if A[i][col]), None)
        if pr is None: continue
        A[rk], A[pr] = A[pr], A[rk]
        inv = INV[A[rk][col]]; A[rk] = [MUL[inv][y] for y in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][col]:
                f = A[i][col]; A[i] = [A[i][j] ^ MUL[f][A[rk][j]] for j in range(7)]
        piv.append(col); rk += 1
    basis = []
    for fc in [c for c in range(7) if c not in piv]:
        u = [0] * 7; u[fc] = 1
        for i, pc in enumerate(piv): u[pc] = A[i][fc]
        basis.append(u)
    for b in basis:
        for row in rows: assert herm1(b, row) == 0
    return basis
def star_all(rows, positions, lastnz):
    """(*) for all a supported on `positions` (rows[j] at positions[j]); if lastnz, only a with a_last != 0"""
    d = len(rows); n = 16 ** d; idx = np.arange(n)
    coefs = [(idx >> (4 * j)) & 15 for j in range(d)]
    keep = coefs[-1] != 0 if lastnz else idx != 0
    V = np.zeros((n, 7), dtype=np.uint8); Wa = np.zeros((n, 7), dtype=np.int64)
    for j in range(d):
        V ^= MULn[coefs[j][:, None], np.array(rows[j], dtype=np.uint8)[None, :]]
        Wa[:, positions[j]] = WTn[coefs[j]]
    V = V[keep]; Wa = Wa[keep]
    ok = True
    for s in range(0, len(V), 1 << 20):
        if np.any(Mw(Wa[s:s + (1 << 20)]) + Mw(WTn[V[s:s + (1 << 20)]]) < THR): ok = False; break
    return ok
nodes = [tuple(int(x, 16) for x in l.split()[2:]) for l in open(sys.argv[2]) if l.startswith('NODE d=4')]
print("depth-4 nodes in dump:", len(nodes))
for t in nodes:
    rows = [unpk(x) for x in t]
    unit = all(herm1(rows[i], rows[j]) == (1 if i == j else 0) for i in range(5) for j in range(5))
    ok5 = star_all(rows, POS[:5], False)
    basis = complement(rows)
    cands = []
    for c0 in range(16):
        for c1 in range(16):
            u = [MUL[c0][basis[0][i]] ^ MUL[c1][basis[1][i]] for i in range(7)]
            if herm1(u, u) == 1: cands.append(u)
    # one representative per mu5-class (scaling by norm-1 elements preserves (*))
    reps = {}
    for u in cands:
        key = min(tuple(MUL[z][y] for y in u) for z in MU5)
        reps[key] = u
    good = [u for u in reps.values() if star_all(rows + [u], POS[:6], True)]
    print("node", ' '.join('%07x' % x for x in t), ": orthonormal=%s, (*) on 5 rows=%s, unit vectors in complement=%d (%d classes), valid 6th rows (position 5)=%d"
          % (unit, ok5, len(cands), len(reps), len(good)))
    sys.stdout.flush()
