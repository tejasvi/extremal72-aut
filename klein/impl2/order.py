"""Row-order heuristics for the search."""
import sys, math, random, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import apply_perm_vec

def con_info(c):
    p = 1.0 - c['nbad'] / 2.0 ** (c['m'] - 1)
    return -math.log2(max(p, 1e-9))

def greedy_order(I, fixed_first=None, pair=True, pool=None):
    """Greedy: repeatedly add the candidate vector (and its beta image) that maximizes the
    information of newly covered constraint orbits. Candidates: low-weight words (pool)."""
    k = I.k
    words = []
    for c in I.cons:
        words.append((c['y'], con_info(c)))
        words.append((apply_perm_vec(I.beta, c['y']), con_info(c)))
    if pool is None:
        pool = [w for w, _ in words]
    order = []
    S = Span()
    def add(v):
        if S.add(v):
            order.append(v)
    if fixed_first:
        for v in fixed_first:
            add(v)
    while S.dim() < k:
        best = None
        cur = [w for w in words if not S.contains(w[0])]
        # candidate evaluation: info gained by adding v (and v beta)
        cand = [v for v in pool if not S.contains(v)]
        if len(cand) > 400:
            cand = random.sample(cand, 400)
        for v in cand:
            T = Span(S.basis())
            T.add(v)
            if pair:
                T.add(apply_perm_vec(I.beta, v))
            gain = sum(inf for w, inf in cur if T.contains(w)) / 2.0
            dd = T.dim() - S.dim()
            score = gain / dd
            if best is None or score > best[0]:
                best = (score, v)
        if best is None:
            # no low-weight candidates left: add arbitrary basis vector
            for b in I.yb0:
                if not S.contains(b):
                    add(b); break
            continue
        v = best[1]
        add(v)
        if pair:
            add(apply_perm_vec(I.beta, v))
    return order

def fixed_space_basis(I):
    """Basis of Y^beta."""
    from structure import solve_affine
    k = I.k
    yb = I.yb0
    bim = [apply_perm_vec(I.beta, y) for y in yb]
    # kernel of 1+beta: combos c with sum c_i (y_i + y_i beta) = 0
    vecs = [yb[i] ^ bim[i] for i in range(k)]
    eqs = []
    for bit in range(I.n2):
        m = 0
        for i in range(k):
            if (vecs[i] >> bit) & 1:
                m |= 1 << i
        eqs.append((m, 0))
    _, ker = solve_affine(eqs, k)
    out = []
    for c in ker:
        v = 0
        for i in range(k):
            if (c >> i) & 1:
                v ^= yb[i]
        out.append(v)
    return out

import numpy as np

class CosetGreedy:
    """Exact greedy over all vectors of Y using coordinates in basis I.yb0."""
    def __init__(self, I):
        self.I = I
        k = I.k
        self.k = k
        # info per coordinate vector
        Sp = Span(I.yb0)
        self.base = I.yb0
        I.set_order(list(I.yb0))  # to get coords()
        info = np.zeros(1 << k, dtype=np.float64)
        for c in I.cons:
            inf = con_info(c)
            y = c['y']; yb = apply_perm_vec(I.beta, y)
            cy = I.coords(y); cyb = I.coords(yb)
            if cy == cyb:
                info[cy] += inf
            else:
                info[cy] += inf / 2; info[cyb] += inf / 2
        self.info = info
        # beta on coordinates: images of basis vectors
        self.bcol = [I.coords(apply_perm_vec(I.beta, b)) for b in I.yb0]
        self.allc = np.arange(1 << k, dtype=np.int64)

    def beta_c(self, c):
        r = 0
        for i in range(self.k):
            if (c >> i) & 1:
                r ^= self.bcol[i]
        return r

    def coset_labels(self, Sbasis):
        """Label of each coordinate vector modulo span(Sbasis) (Sbasis: coordinate ints)."""
        # reduce by echelon basis with pivots; label = reduced vector
        piv = []
        for v in Sbasis:
            for p, b in piv:
                if (v >> p) & 1:
                    v ^= b
            if v:
                piv.append((v.bit_length() - 1, v))
        lab = self.allc.copy()
        for p, b in sorted(piv, reverse=True):
            # full reduction: for entries with bit p set, xor b (process pivots high to low after making basis reduced)
            pass
        # make reduced echelon
        piv.sort(reverse=True)
        red = []
        for p, b in piv:
            for q, c in red:
                if (b >> q) & 1:
                    b ^= c
            red.append((p, b))
        # reduce others too
        red2 = []
        for i, (p, b) in enumerate(red):
            for q, c in red:
                if q != p and (b >> q) & 1:
                    b ^= c
            red2.append((p, b))
        for p, b in red2:
            mask = ((lab >> p) & 1).astype(bool)
            lab[mask] ^= b
        return lab

    def order(self, restrict_first=None, nfirst=None):
        """Greedy order. If restrict_first (list of coordinate vectors spanning a subspace F) and nfirst,
        the first nfirst picks are restricted to F."""
        k = self.k
        Sb = []
        order_c = []
        def inspan(v, basis):
            return rank(basis + [v]) == rank(basis)
        while len(Sb) < k:
            lab = self.coset_labels(Sb)
            sums = np.bincount(lab, weights=self.info, minlength=1 << k)
            valid = np.zeros(1 << k, dtype=bool)
            valid[lab] = True
            sums[~valid] = -1  # not a coset label
            sums[lab[0]] = -1  # the span itself
            if restrict_first is not None and len(order_c) < nfirst:
                Flab = set(int(x) for x in lab[np.array(self.Fall, dtype=np.int64)])
                cand = np.array(sorted(Flab), dtype=np.int64)
                cand = cand[sums[cand] >= 0]
                if len(cand) == 0:
                    best = None
                else:
                    best = int(cand[np.argmax(sums[cand])])
            else:
                best = int(np.argmax(sums))
                if sums[best] < 0:
                    best = None
            if best is None:
                break
            # representative: the label itself is a reduced vector in that coset
            v = best
            Sb.append(v); order_c.append(v)
            vb = self.beta_c(v)
            if not inspan(vb, Sb):
                Sb.append(vb); order_c.append(vb)
        # convert to vectors
        vecs = []
        for c in order_c:
            v = 0
            for i in range(k):
                if (c >> i) & 1:
                    v ^= self.base[i]
            vecs.append(v)
        return vecs

def best_order(I, verbose=False, cost_child=0.05):
    """Try F-first with switch points; return (order, estimated work)."""
    G = CosetGreedy(I)
    F = fixed_space_basis(I)
    Fc = [I.coords(f) for f in F] if False else None
    I.set_order(list(I.yb0))
    Fcoords = [I.coords(f) for f in F]
    # all elements of F in coordinates
    Fall = [0]
    for f in Fcoords:
        Fall = Fall + [x ^ f for x in Fall]
    G.Fall = Fall
    results = []
    for nf in range(0, len(F) + 1):
        o = G.order(restrict_first=Fcoords, nfirst=nf)
        I.set_order(o)
        w = work_estimate(I, cost_child)
        results.append((w, nf, o))
        if verbose:
            print('  nfirst', nf, 'log2 work %.2f' % w, 'k_t', I.k_t)
    results.sort(key=lambda r: r[0])
    w, nf, o = results[0]
    I.set_order(o)
    return o, w, nf

def work_estimate(I, cost_child=0.05):
    k = I.k
    info = [0.0] * k
    ncon = [0] * k
    for c, lev in zip(I.cons, I.con_level):
        info[lev] += con_info(c)
        ncon[lev] += 1
    logN = 0.0
    tot = 0.0
    for t in range(k):
        tot += 2.0 ** logN * (ncon[t] + cost_child * 2.0 ** I.k_t[t] + 1)
        logN = logN + I.k_t[t] - info[t]
    return math.log2(tot)

def reachable_info(I):
    """Per-constraint information using the reachable syndrome set: syndromes of y over all valid B form an
    affine subspace A_y (gauge-invariant); p_bad = |Bad cap A_y| / |A_y|. Requires I.set_order done.
    Returns list of info values aligned with I.cons."""
    k = I.k
    # Gram matrices of part and all homogeneous generators (H + gauge pivots irrelevant: use H only,
    # since gauge does not change syndromes)
    def gram(vec):
        G = np.zeros((k, k), dtype=np.int64)
        for i in range(k):
            for l in range(k):
                G[i, l] = (vec >> I.idx[(i, l)]) & 1
        return G
    Gp = gram(I.part)
    Hs = np.array([gram(h) for h in I.H])  # N x k x k
    infos = []
    for c in I.cons:
        y = c['y']
        cy = np.array([(I.coords(y) >> i) & 1 for i in range(k)], dtype=np.int64)
        D = np.array([[(I.coords(x) >> i) & 1 for i in range(k)] for x in c['X']], dtype=np.int64)  # m x k
        const = (cy @ Gp @ D.T) % 2  # m
        lin = (np.einsum('i,sil,jl->sj', cy, Hs, D)) % 2  # N x m
        # column space of lin^T (as m-bit ints)
        cols = []
        for s in range(lin.shape[0]):
            v = 0
            for j in range(lin.shape[1]):
                if lin[s, j]:
                    v |= 1 << j
            cols.append(v)
        Sp = Span(cols)
        cv = 0
        for j in range(len(const)):
            if const[j]:
                cv |= 1 << j
        nb = sum(1 for b in c['bad'] if Sp.contains(b ^ cv))
        tot = 1 << Sp.dim()
        p = 1.0 - nb / tot
        infos.append(-math.log2(max(p, 1e-12)))
    return infos

def image_space_basis(I):
    """Basis of (1+beta)Y."""
    return echelon([y ^ apply_perm_vec(I.beta, y) for y in I.yb0])

class CosetGreedy2(CosetGreedy):
    """CosetGreedy with externally supplied per-constraint information (aligned with I.cons)."""
    def __init__(self, I, infos):
        self.I = I
        k = I.k
        self.k = k
        self.base = I.yb0
        I.set_order(list(I.yb0))
        info = np.zeros(1 << k, dtype=np.float64)
        for c, inf in zip(I.cons, infos):
            y = c['y']; yb = apply_perm_vec(I.beta, y)
            cy = I.coords(y); cyb = I.coords(yb)
            if cy == cyb:
                info[cy] += inf
            else:
                info[cy] += inf / 2; info[cyb] += inf / 2
        self.info = info
        self.bcol = [I.coords(apply_perm_vec(I.beta, b)) for b in I.yb0]
        self.allc = np.arange(1 << k, dtype=np.int64)

    def order_sched(self, sched):
        """sched: list of (list of allowed coordinate vectors (a subspace's elements), number of picks)."""
        k = self.k
        Sb = []
        order_c = []
        def inspan(v, basis):
            return rank(basis + [v]) == rank(basis)
        phase = 0
        picks = 0
        while len(Sb) < k:
            lab = self.coset_labels(Sb)
            sums = np.bincount(lab, weights=self.info, minlength=1 << k)
            valid = np.zeros(1 << k, dtype=bool)
            valid[lab] = True
            sums[~valid] = -1
            sums[lab[0]] = -1
            while phase < len(sched) and picks >= sched[phase][1]:
                phase += 1; picks = 0
            best = None
            if phase < len(sched):
                allowed = sched[phase][0]
                cand = np.unique(lab[np.array(allowed, dtype=np.int64)])
                cand = cand[sums[cand] >= 0]
                if len(cand):
                    best = int(cand[np.argmax(sums[cand])])
                else:
                    phase += 1; picks = 0
                    continue
            else:
                best = int(np.argmax(sums))
                if sums[best] < 0:
                    break
            v = best
            Sb.append(v); order_c.append(v); picks += 1
            vb = self.beta_c(v)
            if not inspan(vb, Sb):
                Sb.append(vb); order_c.append(vb)
        vecs = []
        for c in order_c:
            v = 0
            for i in range(k):
                if (c >> i) & 1:
                    v ^= self.base[i]
            vecs.append(v)
        return vecs

def work_estimate2(I, infos, cost_child=0.05):
    k = I.k
    info = [0.0] * k
    ncon = [0] * k
    for inf, lev in zip(infos, I.con_level):
        info[lev] += inf
        ncon[lev] += 1
    logN = 0.0
    tot = 0.0
    for t in range(k):
        tot += 2.0 ** logN * (ncon[t] + cost_child * 2.0 ** I.k_t[t] + 1)
        logN = max(logN + I.k_t[t] - info[t], -50)
    return math.log2(tot)

def best_order2(I, verbose=False):
    I.set_order(list(I.yb0))
    infos = reachable_info(I)
    G = CosetGreedy2(I, infos)
    I.set_order(list(I.yb0))
    F = fixed_space_basis(I)
    Im = image_space_basis(I)
    def allc(basis):
        cs = [I.coords(b) for b in basis]
        out = [0]
        for c in cs:
            out = out + [x ^ c for x in out]
        return out
    Fall = allc(F)
    Iall = allc(Im)
    scheds = []
    for nf in range(0, len(F) + 1):
        scheds.append(("F%d" % nf, [(Fall, nf)]))
    for ni in range(1, len(Im) + 1):
        scheds.append(("I%d+F" % ni, [(Iall, ni), (Fall, len(F))]))
    results = []
    for name, sc in scheds:
        o = G.order_sched(sc)
        I.set_order(o)
        w = work_estimate2(I, infos)
        results.append((w, name, o, list(I.k_t)))
        if verbose:
            print('  %-8s log2 work %.2f k_t %s' % (name, w, I.k_t))
    results.sort(key=lambda r: r[0])
    w, name, o, kt = results[0]
    I.set_order(o)
    I.infos = infos
    return o, w, name
