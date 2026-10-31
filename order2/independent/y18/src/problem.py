"""Problem builder for: forms B on a self-dual code Y (length n, dim k = n/2) such that C_B has minimum weight >= dd.

Conventions
- vectors: Python ints, bit i = coordinate i.
- A form B is given by its Gram matrix M in the basis G of Y: M[i] = int bitmask, bit j = B(G[i], G[j]).
- Functionals on forms are ints over the upper-triangular entry index idx[i][j] (FormSpace in forms.py):
  the functional "B(y,x)" evaluated on M is popcount(func & Mvec) mod 2, Mvec = upper-triangular bit vector of M.
- Weight classes: for |y| = w < dd with w = dd - 2t (t >= 1), codewords (z|z+y) have weight w + 2|z outside S|,
  doubly-even forces |z outside S| = t mod 2, so the forbidden values of |e| are E(w) = {t-2, t-4, ...} >= 0, i.e.
  {e : |e| < (dd - w)/2, |e| = (dd-w)/2 mod 2}.  For dd=16: E(8)={0,2}, E(10)={1}, E(12)={0}; E(14) = {} (|e|>=1 auto).
"""
import sys
sys.path.insert(0, "<HOME>/c72_indep/y18/src")
from codes import *
from forms import FormSpace
from itertools import combinations


def forbidden_e_weights(w, dd):
    t = (dd - w) // 2
    return [s for s in range(t - 2, -1, -2)] if t >= 1 else []


class Problem:
    def __init__(self, G, n, dd):
        self.G = list(G)
        self.n = n
        self.k = len(G)
        assert 2 * self.k == n
        self.dd = dd
        self.ones = (1 << n) - 1
        # sanity: self-dual
        for a in G:
            for b in G:
                assert dot(a, b) == 0
        assert rank(G, n) == self.k
        self.words = span(G)
        self.wordset = set(self.words)
        assert self.ones in self.wordset
        self.FS = FormSpace(G, n)
        k = self.k
        # diag functionals: B(y,y) + B(y,1) = |y|/2 mod 2, for y in basis
        self.diag = [(self.FS.functional(g, g) ^ self.FS.functional(g, self.ones), (wt(g) // 2) & 1) for g in G]
        # gauge forms D_i(y,y') = y_i y'_i as Gram upper-tri vectors
        self.gauge = []
        for i in range(n):
            M = 0
            for a in range(k):
                for b in range(a, k):
                    if (G[a] >> i & 1) and (G[b] >> i & 1):
                        M |= 1 << self.FS.idx[a][b]
            self.gauge.append(M)
        # low-weight words: weights w with nonempty E(w)
        self.Eof = {w: forbidden_e_weights(w, dd) for w in range(0, dd, 2)}
        self.low = [y for y in self.words if y and wt(y) < dd and self.Eof[wt(y)]]

    def shortened_basis(self, y):
        """Basis of Y_y = {x in Y : x & y == 0} (as list of ints)."""
        G, n = self.G, self.n
        supp = [i for i in range(n) if y >> i & 1]
        vecs = []
        for g in G:
            r = 0
            for a, i in enumerate(supp):
                if g >> i & 1:
                    r |= 1 << a
            vecs.append(r)
        ech, kern = [], []
        for t, v in enumerate(vecs):
            comb = 1 << t
            for (r, rc) in ech:
                if v >> ((r & -r).bit_length() - 1) & 1:
                    v ^= r
                    comb ^= rc
            if v:
                p = v & -v
                ech = [(r ^ v, rc ^ comb) if r & p else (r, rc) for (r, rc) in ech]
                ech.append((v, comb))
            else:
                kern.append(comb)
        out = []
        for comb in kern:
            x = 0
            for t in range(self.k):
                if comb >> t & 1:
                    x ^= G[t]
            assert x & y == 0 and x in self.wordset
            out.append(x)
        assert rank(out, n) == len(out)
        return out

    def forbidden_syndromes(self, y, xb):
        """Set of syndromes (int, bit j = <e, xb[j]>) of vectors e supported outside y with |e| in E(|y|)."""
        T = [i for i in range(self.n) if not y >> i & 1]
        out = set()
        for s in self.Eof[wt(y)]:
            for c in combinations(T, s):
                e = 0
                for i in c:
                    e |= 1 << i
                out.add(sum((wt(e & x) & 1) << j for j, x in enumerate(xb)))
        return out

    # ---------- forms ----------
    def gram_to_vec(self, M):
        v = 0
        for i in range(self.k):
            for j in range(i, self.k):
                if M[i] >> j & 1:
                    v |= 1 << self.FS.idx[i][j]
        return v

    def vec_to_gram(self, v):
        k = self.k
        M = [0] * k
        for i in range(k):
            for j in range(i, k):
                if v >> self.FS.idx[i][j] & 1:
                    M[i] |= 1 << j
                    M[j] |= 1 << i
        return M

    def is_valid_form(self, M):
        """symmetric + diag condition B(y,y) = |y|/2 + B(y,1) for all basis y (linear => for all y)."""
        k = self.k
        for i in range(k):
            for j in range(k):
                if (M[i] >> j & 1) != (M[j] >> i & 1):
                    return False
        onesc = self.FS.coords(self.ones)
        for i in range(k):
            Byy = M[i] >> i & 1
            By1 = wt(M[i] & onesc) & 1
            if Byy != ((wt(self.G[i]) // 2) & 1) ^ By1:
                return False
        return True

    def B(self, M, y, x):
        a, b = self.FS.coords(y), self.FS.coords(x)
        s = 0
        for i in range(self.k):
            if a >> i & 1:
                s ^= wt(M[i] & b) & 1
        return s

    def z0_rows(self, M):
        """For each basis vector g_i, a vector z with <z, g_j> = M[i]_j for all j (exists: Y self-dual)."""
        n, k, G = self.n, self.k, self.G
        # equations <z, g_j> = rhs_j: row-reduce the g_j tracking combinations (r = sum_{j in rc} g_j, pivot p)
        ech = []
        for j in range(k):
            v, c = G[j], 1 << j
            for (r, rc, p) in ech:
                if v >> p & 1:
                    v ^= r
                    c ^= rc
            assert v
            p = (v & -v).bit_length() - 1
            ech = [(r ^ v, rc ^ c, pp) if r >> p & 1 else (r, rc, pp) for (r, rc, pp) in ech]
            ech.append((v, c, p))
        out = []
        for i in range(k):
            rhs = M[i]
            z = 0
            for (r, rc, p) in ech:
                # row r = sum_{j in rc} g_j ; equation <z, r> = sum_{j in rc} rhs_j ; pivot p only in this row
                val = wt(rc & rhs) & 1
                if val:
                    z |= 1 << p
            for j in range(k):
                assert dot(z, G[j]) == (rhs >> j & 1)
            out.append(z)
        return out

    def code_CB(self, M):
        """Generator rows of C_B (length 2n, bit i = (i,0), bit n+i = (i,1))."""
        n = self.n
        rows = [g | (g << n) for g in self.G]
        for g, z in zip(self.G, self.z0_rows(M)):
            rows.append(z | ((z ^ g) << n))
        return rows
