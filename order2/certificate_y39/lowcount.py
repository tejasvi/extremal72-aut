"""Low-weight word counts of C_B for random symmetric forms B on Y (diagonal condition B(y,y) = |y|/2 + B(y,1)).
For each low word y (|y| < d with a constraint), precompute a basis u_1..u_r of Y_y and the table
cnt_y[syndrome] = number of small patterns e (outside supp y, |e| < (d-|y|)/2) with that syndrome, by size.
X(B) = sum_y cnt_y[s_y(B)] = (number of codewords of weight < d)/2 when m_y = 2 for all low y."""
import numpy as np
import random
from itertools import combinations
from mc import span_np, pc, reduce_basis


def basis_with_ones(gens, n2):
    """basis of span(gens) whose first element is the all-ones vector (must be in the code)"""
    ones = (1 << n2) - 1
    basis = [ones]
    piv = reduce_basis([ones])
    for g in gens:
        v = g
        for b in sorted(piv, reverse=True):
            if (v >> b) & 1:
                v ^= piv[b]
        if v:
            basis.append(g)
            piv = reduce_basis(basis)
    assert len(basis) == len(gens)
    return basis


class LowCounter:
    def __init__(self, gens, n2, d):
        self.n2, self.d = n2, d
        self.basis = basis_with_ones(gens, n2)
        k = len(self.basis)
        self.k = k
        # coordinates: solve via echelon with tracking
        piv = {}
        for i, g in enumerate(self.basis):
            v, c = g, 1 << i
            for b in sorted(piv, reverse=True):
                if (v >> b) & 1:
                    v ^= piv[b][0]
                    c ^= piv[b][1]
            piv[v.bit_length() - 1] = (v, c)
        self._piv = sorted(piv.items(), reverse=True)
        Y = span_np(self.basis)
        self.Y = Y
        wy = np.bitwise_count(Y)
        self.words = []       # (y, coords(y), [coords(u_j)], cnt dict by size)
        for j in range(1, d):
            if j % 2:
                continue
            sizes = [s for s in range(0, (d - j + 1) // 2) if s % 2 == (j // 2) % 2]
            if not sizes:
                continue
            for y in Y[wy == j].tolist():
                y = int(y)
                sh = Y[(Y & np.uint64(y)) == 0]
                bas = list(reduce_basis([int(u) for u in sh.tolist()]).values())
                # syndrome of a pattern e: bits <e, u_j>
                outside = [i for i in range(n2) if not (y >> i) & 1]
                cnt = {}
                for s in sizes:
                    for comb_ in combinations(outside, s):
                        e = 0
                        for i in comb_:
                            e |= 1 << i
                        syn = 0
                        for t, u in enumerate(bas):
                            syn |= (pc(e & u) & 1) << t
                        cnt.setdefault(s, {})
                        cnt[s][syn] = cnt[s].get(syn, 0) + 1
                self.words.append((y, self.coords(y), [self.coords(u) for u in bas], cnt, j))

    def coords(self, w):
        c = 0
        for b, (v, cc) in self._piv:
            if (w >> b) & 1:
                w ^= v
                c ^= cc
        assert w == 0
        return c

    def random_gram(self, rng):
        k = self.k
        M = np.zeros((k, k), dtype=np.int64)
        for i in range(k):
            for j in range(i + 1, k):
                M[i, j] = M[j, i] = rng.getrandbits(1)
        M[0, 0] = rng.getrandbits(1)
        for i in range(1, k):
            M[i, i] = ((pc(self.basis[i]) // 2) + M[i, 0]) % 2
        return M

    def check_gram(self, M):
        """diagonal condition B(y,y) = |y|/2 + B(y,1) for basis vectors (1 = basis[0])"""
        for i in range(self.k):
            if M[i, i] % 2 != ((pc(self.basis[i]) // 2) + M[i, 0]) % 2:
                return False
        return True

    def counts(self, M):
        """returns dict (j, size) -> total count"""
        k = self.k
        out = {}
        for (y, cy, cus, cnt, j) in self.words:
            vy = np.array([(cy >> i) & 1 for i in range(k)], dtype=np.int64)
            row = (vy @ M) % 2        # B(y, g_i)
            syn = 0
            for t, cu in enumerate(cus):
                b = 0
                cc = cu
                i = 0
                while cc:
                    if cc & 1:
                        b ^= int(row[i])
                    cc >>= 1
                    i += 1
                syn |= b << t
            for s, tab in cnt.items():
                out[(j, s)] = out.get((j, s), 0) + tab.get(syn, 0)
        return out
