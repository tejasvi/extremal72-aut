"""Linear algebra for symmetric bilinear forms on a self-dual code Y with basis G (k vectors).
A form is a symmetric k x k matrix M over F2; we index its upper-triangular entries (i<=j) by idx[i][j].
The functional 'B(y,x)' (y,x in Y) is the 0/1 vector over those entries."""
import sys
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from codes import *


class FormSpace:
    def __init__(self, G, n):
        self.G = list(G)
        self.n = n
        self.k = k = len(G)
        self.idx = [[None] * k for _ in range(k)]
        c = 0
        for i in range(k):
            for j in range(i, k):
                self.idx[i][j] = self.idx[j][i] = c
                c += 1
        self.N = c
        # coordinates of codewords in the basis: solve via reduced echelon with tracking
        self._ech = []  # (vec, combo)
        for t, g in enumerate(G):
            v, comb = g, 1 << t
            for (r, rc) in self._ech:
                if v >> ((r & -r).bit_length() - 1) & 1:
                    v ^= r; comb ^= rc
            assert v, "basis vectors dependent"
            p = v & -v
            self._ech = [(r ^ v, rc ^ comb) if r & p else (r, rc) for (r, rc) in self._ech]
            self._ech.append((v, comb))

    def coords(self, y):
        """coefficient vector (int, bit t for G[t]) of y in basis G; asserts y in span."""
        comb = 0
        v = y
        for (r, rc) in self._ech:
            if v >> ((r & -r).bit_length() - 1) & 1:
                v ^= r; comb ^= rc
        assert v == 0, "not in code"
        return comb

    def functional(self, y, x):
        """vector over upper-tri entries for B(y,x)."""
        a, b = self.coords(y), self.coords(x)
        f = 0
        k = self.k
        for i in range(k):
            if a >> i & 1:
                for j in range(k):
                    if b >> j & 1:
                        f ^= 1 << self.idx[i][j]
        return f

    def eval(self, M, y, x):
        """M: list of k ints (row i bitmask over j). B(y,x)."""
        a, b = self.coords(y), self.coords(x)
        s = 0
        for i in range(self.k):
            if a >> i & 1:
                s ^= wt(M[i] & b) & 1
        return s
