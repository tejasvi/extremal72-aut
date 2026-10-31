"""Build a search instance: Y (self-dual, length n2, dim k=n2/2), beta (fpf involution in Aut(Y)),
target distance d of the length-2*n2 code C = {(z, z+y) : y in Y, z in z0(y) + Y}.

Parametrisation: B(y,y') = <z0(y), y'> is a symmetric bilinear form on Y with
  (beta)  B(y beta, y' beta) = B(y, y')
  (de)    B(y,y) + B(y,1) = wt(y)/2 mod 2
Gauge: B ~ B + D_T, D_T(y,y') = |y & y' & T| mod 2, T a union of beta-orbits or a beta-transversal.
Distance: for y in Y of weight w (0<w<d): no e subset of S^c=supp(y)^c with |e| in E_w lies in the
coset z0(y)|S^c + Y|S^c, where E_w = {j < (d-w)/2 : j = w/2 mod 2}; equivalently the syndrome
(B(y,x))_{x in basis of Y_{S^c}} differs from (<e,x>)_x for every such e.
"""
import sys, math, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import apply_perm_vec
import numpy as np

def kernel_basis_of_restriction(basis, mask):
    """Basis of {x in span(basis): x & mask == 0} (returned as vectors)."""
    # eliminate on coordinates in mask
    rows = [(b & mask, b) for b in basis]
    piv = []  # (bit, rowmask, vec)
    kern = []
    for rm, v in rows:
        for p, pm, pv in piv:
            if (rm >> p) & 1:
                rm ^= pm; v ^= pv
        if rm:
            piv.append((rm.bit_length() - 1, rm, v))
        else:
            kern.append(v)
    return echelon(kern)

class Instance:
    def __init__(self, Ybasis, beta, d, name=""):
        self.name = name
        self.beta = list(beta)
        self.n2 = len(beta)
        self.yb0 = echelon(list(Ybasis))
        self.k = len(self.yb0)
        assert 2 * self.k == self.n2
        self.d = d
        self.one = (1 << self.n2) - 1
        assert Span(self.yb0).contains(self.one)
        for y in self.yb0:
            assert Span(self.yb0).contains(apply_perm_vec(self.beta, y))
        assert all(beta[beta[i]] == i and beta[i] != i for i in range(self.n2))
        self._low_words()

    def _low_words(self):
        arr = span_array(self.yb0)
        w = popcount_array(arr)
        sel = (w > 0) & (w < self.d)
        words = [int(x) for x in arr[sel]]
        dY = int(w[w > 0].min())
        assert 2 * dY >= self.d, "Y has too small minimum distance"
        self.dY = dY
        # one representative per beta-orbit
        seen = set()
        self.orbits = []  # list of (y, ybeta)
        for y in sorted(words):
            if y in seen:
                continue
            yb = apply_perm_vec(self.beta, y)
            seen.add(y); seen.add(yb)
            self.orbits.append((y, yb))
        self.cons = []
        for (y, yb) in self.orbits:
            c = self._constraint(y)
            if c['nbad'] > 0:
                self.cons.append(c)

    def _constraint(self, y):
        wy = popcount(y)
        S = y
        Sc = self.one ^ S
        X = kernel_basis_of_restriction(self.yb0, S)  # codewords disjoint from supp(y)
        m = len(X)
        E = [j for j in range((self.d - wy + 1) // 2) if j % 2 == (wy // 2) % 2 and 2 * j < self.d - wy]
        comp = [i for i in range(self.n2) if (Sc >> i) & 1]
        # syndrome of a single coordinate i: bits <e_i, x_j>
        col = {}
        for i in comp:
            s = 0
            for j, x in enumerate(X):
                if (x >> i) & 1:
                    s |= 1 << j
            col[i] = s
        bad = set()
        from itertools import combinations
        for j in E:
            for es in combinations(comp, j):
                s = 0
                for i in es:
                    s ^= col[i]
                bad.add(s)
        # parity bit check: 1+y is in Y_{S^c}; its syndrome bit equals |e| mod 2 = wt(y)/2
        return dict(y=y, w=wy, X=X, m=m, E=E, bad=sorted(bad), nbad=len(bad))

    # ---------- parametrisation for a given ordered basis -------------
    def set_order(self, wbasis, use_transversal=True):
        """wbasis: ordered list of k vectors forming a basis of Y."""
        k = self.k
        assert rank(wbasis) == k and all(Span(self.yb0).contains(w) for w in wbasis)
        self.w = list(wbasis)
        # coordinates helper
        self._cb = []  # elimination structure for coordinates in w-basis
        piv = []
        for i, b in enumerate(self.w):
            tag = 1 << i
            for p, pb, pt in piv:
                if (b >> p) & 1:
                    b ^= pb; tag ^= pt
            piv.append((b.bit_length() - 1, b, tag))
        self._piv = piv
        # variable index for (i,l), i<=l, row-major
        idx = {}
        t = 0
        self.entry_row = []
        for i in range(k):
            for l in range(i, k):
                idx[(i, l)] = t; idx[(l, i)] = t
                self.entry_row.append(i)
                t += 1
        self.idx = idx
        self.nent = t
        bco = [self.coords(apply_perm_vec(self.beta, wv)) for wv in self.w]
        cone = self.coords(self.one)
        def fmask(ci, cj):
            m = 0
            for i in range(k):
                if (ci >> i) & 1:
                    for j in range(k):
                        if (cj >> j) & 1:
                            m ^= 1 << idx[(i, j)]
            return m
        eqs = []
        for i in range(k):
            for l in range(i, k):
                eqs.append((fmask(bco[i], bco[l]) ^ (1 << idx[(i, l)]), 0))
        for i in range(k):
            eqs.append(((1 << idx[(i, i)]) ^ fmask(1 << i, cone), (popcount(self.w[i]) // 2) & 1))
        from structure import solve_affine
        part, hom = solve_affine(eqs, self.nent)
        self.part = part
        # gauge
        orbs = []
        seenp = set()
        for i in range(self.n2):
            if i not in seenp:
                orbs.append((i, self.beta[i])); seenp |= {i, self.beta[i]}
        def DT(T):
            m = 0
            for i in range(k):
                for l in range(i, k):
                    if popcount(self.w[i] & self.w[l] & T) & 1:
                        m |= 1 << idx[(i, l)]
            return m
        gauge = [DT((1 << i) | (1 << j)) for (i, j) in orbs]
        tr = 0
        for (i, j) in orbs:
            tr |= 1 << i
        if use_transversal:
            gauge.append(DT(tr))
        # echelon with pivot = lowest set bit, gauge first
        pivd = {}
        def reduce_low(v):
            while v:
                p = (v & -v).bit_length() - 1
                if p in pivd:
                    v ^= pivd[p]
                else:
                    return v, p
            return 0, None
        ng = 0
        for g in gauge:
            v, p = reduce_low(g)
            if v:
                pivd[p] = v; ng += 1
        self.gauge_rank = ng
        self.gauge_pivots = sorted(pivd.keys())
        H = []
        for h in hom:
            v, p = reduce_low(h)
            if v:
                pivd[p] = v
                H.append((p, v))
        H.sort()
        self.H = [v for p, v in H]
        self.var_level = [self.entry_row[p] for p, v in H]
        self.N = len(self.H)
        # check: gauge pivots are all valid
        assert ng + self.N == len(hom)
        self.k_t = [self.var_level.count(t) for t in range(k)]
        # constraint levels
        self.con_level = []
        for c in self.cons:
            y = c['y']; yb = apply_perm_vec(self.beta, y)
            l1 = self.coords(y).bit_length() - 1
            l2 = self.coords(yb).bit_length() - 1
            self.con_level.append(min(l1, l2))
        return self

    def coords(self, v):
        tag = 0
        for p, pb, pt in self._piv:
            if (v >> p) & 1:
                v ^= pb; tag ^= pt
        assert v == 0
        return tag

    def estimate(self, verbose=False):
        """Heuristic tree size: N_t = N_{t-1} * 2^{k_t} * prod p_y (level t)."""
        k = self.k
        info = [0.0] * k
        ncon = [0] * k
        for c, lev in zip(self.cons, self.con_level):
            p = 1.0 - c['nbad'] / 2.0 ** (c['m'] - 1)
            p = max(p, 1e-9)
            info[lev] += -math.log2(p)
            ncon[lev] += 1
        logN = 0.0
        tot = 0.0
        rows = []
        for t in range(k):
            work = logN + self.k_t[t]  # children generated
            tot += 2.0 ** work
            logN = logN + self.k_t[t] - info[t]
            rows.append((t, self.k_t[t], ncon[t], round(info[t], 1), round(work, 1), round(logN, 1)))
        if verbose:
            for r in rows:
                print("  level %2d new vars %2d  cons %5d  info %6.1f  log2(children) %5.1f  log2(survivors) %6.1f" % r)
        return math.log2(tot), rows
