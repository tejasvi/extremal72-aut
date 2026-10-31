"""Parity certificate search.  Features: for each Aut(Y)-orbit O of low words (|y| in {8,10,12}) and each bad-syndrome
type t = (pattern size, multiplicity of the syndrome among small patterns), f_{O,t}(B) = sum_{y in O} sum_{v bad, type t}
[s_y(B) = v].  A certificate is an F2-combination of features equal to 1 for every form B (then some bad event occurs
for every B, so no extremal code).  We sample random forms, compute features mod 2 and solve the F2 system."""
import sys, random, time, pickle
import numpy as np
from itertools import combinations
sys.path.insert(0, '<HOME>/c72/c2opt/math')
from mc import span_np, pc, reduce_basis, load_codes
from lowcount import basis_with_ones
from autil import word_orbits


class PCS:
    def __init__(self, gens, n2, d, ci=None, orbits=True, verbose=True):
        t0 = time.time()
        self.n2, self.d = n2, d
        self.basis = basis_with_ones(gens, n2)
        k = len(self.basis)
        self.k = k
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
        wy = np.bitwise_count(Y)
        words = []
        for j in range(1, d):
            if j % 2:
                continue
            sizes = [s for s in range(0, (d - j + 1) // 2) if s % 2 == (j // 2) % 2]
            if sizes:
                words += [int(y) for y in Y[wy == j].tolist()]
        if orbits and ci is not None:
            orbs = word_orbits(ci, words)
        else:
            orbs = [[w] for w in words]
        orb_of = {}
        for oi, o in enumerate(orbs):
            for w in o:
                orb_of[w] = oi
        self.orbs = orbs
        R = max(10, 1)
        self.wlist = []
        feat_index = {}
        tabs = []
        cys = []
        ubs = []
        rmax = 0
        for y in words:
            j = pc(y)
            sizes = [s for s in range(0, (d - j + 1) // 2) if s % 2 == (j // 2) % 2]
            sh = Y[(Y & np.uint64(y)) == 0]
            comp = ((1 << n2) - 1) ^ y
            # basis of Y_y with comp first (its syndrome bit is fixed), we keep the others
            bas = [comp]
            cur = reduce_basis([comp])
            for u in sh.tolist():
                u = int(u)
                v = u
                for b in sorted(cur, reverse=True):
                    if (v >> b) & 1:
                        v ^= cur[b]
                if v:
                    bas.append(u)
                    cur = reduce_basis(bas)
            bas = bas[1:]
            r = len(bas)
            rmax = max(rmax, r)
            outside = [i for i in range(n2) if not (y >> i) & 1]
            mult = {}
            for s in sizes:
                for cmb in combinations(outside, s):
                    e = 0
                    for i in cmb:
                        e |= 1 << i
                    syn = 0
                    for t, u in enumerate(bas):
                        syn |= (pc(e & u) & 1) << t
                    mult.setdefault(syn, []).append(s)
            tab = {}
            for syn, ss in mult.items():
                typ = (orb_of[y], tuple(sorted(ss)))
                if typ not in feat_index:
                    feat_index[typ] = len(feat_index)
                tab[syn] = feat_index[typ]
            tabs.append(tab)
            cys.append(self.coords(y))
            ubs.append([self.coords(u) for u in bas])
        self.words = words
        self.feat = sorted(feat_index, key=lambda t: feat_index[t])
        self.nfeat = len(self.feat)
        nw = len(words)
        self.rmax = rmax
        self.T = np.full((nw, 1 << rmax), -1, dtype=np.int32)
        for wi, tab in enumerate(tabs):
            for syn, fi in tab.items():
                self.T[wi, syn] = fi
        self.CY = np.array([[(c >> i) & 1 for i in range(k)] for c in cys], dtype=np.int64)
        self.UB = np.zeros((nw, rmax, k), dtype=np.int64)
        for wi, ub in enumerate(ubs):
            for t, c in enumerate(ub):
                self.UB[wi, t] = [(c >> i) & 1 for i in range(k)]
        self.pw = (1 << np.arange(rmax)).astype(np.int64)
        if verbose:
            print(f"PCS: {nw} low words, {len(orbs)} orbits, {self.nfeat} features, rmax {rmax} [{time.time() - t0:.1f}s]", flush=True)

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

    def syndromes(self, M):
        R = (self.CY @ M) % 2                              # nw x k
        S = np.einsum('wk,wtk->wt', R, self.UB) % 2        # nw x rmax
        return S @ self.pw

    def features(self, M):
        syn = self.syndromes(M)
        fi = self.T[np.arange(len(self.words)), syn]
        f = np.zeros(self.nfeat, dtype=np.int64)
        np.add.at(f, fi[fi >= 0], 1)
        return f


def f2_solve(rows, rhs):
    """solve rows (list of python int bitmasks over features) x = rhs bits over F2; returns solution mask or None.
    Also returns rank."""
    piv = {}   # pivot bit -> (row mask, rhs bit)
    for r, b in zip(rows, rhs):
        v, c = r, b
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h][0]
                c ^= piv[h][1]
            else:
                piv[h] = (v, c)
                break
        else:
            if c:
                return None, len(piv)
    # back-substitute: free vars = 0
    sol = 0
    for h in sorted(piv):
        v, c = piv[h]
        # value of x_h = c + sum_{other bits in v} x_bit
        rest = v & ~(1 << h)
        val = c ^ (bin(rest & sol).count('1') & 1)
        if val:
            sol |= 1 << h
    return sol, len(piv)
