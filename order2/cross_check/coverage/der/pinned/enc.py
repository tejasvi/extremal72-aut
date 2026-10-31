"""CNF / CNF+XOR encoder for one cube of an lwe instance (sat).

Instance (mkinst.py format): N variables (bit v of asg = variable v), constraints (lv, wt, m, forms, bad); the syndrome
s_j = parity(forms[j] & x) ^ fc[j] must avoid bad.  A cube fixes variables 0..nfix-1 to the bits of asg.

Per constraint, after substituting the cube: the free parts of the m forms span a space of rank r (one combination
is always constant: the 1+y bit, so r <= m-1).  A basis b_1..b_r of that row space is chosen with minimum total
weight (greedy over all 2^r-1 vectors of the space, exact for this matroid); z_i = <b_i, x>.  Every z in F2^r is
reachable, and Bad' = {z : s(z) in bad}.  The clauses exclude Bad' (DIRECT: one clause per point; PRIME: a greedy
cover by prime implicants; ALLPRIME: all prime implicants).  z_i are auxiliary variables defined by XORs (shared
between equal masks; a mask of weight 1 is the base variable itself).

Output: DIMACS with CryptoMiniSat 'x' lines (XOR mode) or pure CNF with Tseitin XOR chains (CNF mode).
Variables 1..nF are the free base variables in order (variable nfix+k -> k+1).
"""
import sys, os, itertools, random

def parse(fn):
    tok = open(fn).read().split(); p = 0
    N, NLEV, NC = int(tok[0]), int(tok[1]), int(tok[2]); p = 3
    vstart = [int(t) for t in tok[p:p + NLEV + 1]]; p += NLEV + 1
    cons = []
    for _ in range(NC):
        lv, wt, m, nbad = int(tok[p]), int(tok[p + 1]), int(tok[p + 2]), int(tok[p + 3]); p += 4
        fm = []; fc = []
        for s in range(m):
            fm.append(int(tok[p], 16)); fc.append(int(tok[p + 1])); p += 2
        bad = frozenset(int(t) for t in tok[p:p + nbad]); p += nbad
        cons.append((lv, wt, m, fm, fc, bad))
    return N, NLEV, vstart, cons

def par(x):
    return x.bit_count() & 1

def reduce_con(fm, fc, bad, fixmask, asg):
    """Returns ('det', ok) if all forms are fixed, else ('free', basis masks [r], Bad' as a set of ints in [0, 2^r))."""
    m = len(fm)
    rows = [f & ~fixmask for f in fm]
    cst = [c ^ par(f & fixmask & asg) for f, c in zip(fm, fc)]
    if not any(rows):
        s = sum(c << j for j, c in enumerate(cst))
        return ('det', s not in bad)
    # row-space basis (echelon by highest bit) of the free parts
    ech = []                              # list of (pivotbit, vec)
    for v in rows:
        for pb, e in ech:
            if (v >> pb) & 1: v ^= e
        if v: ech.append((v.bit_length() - 1, v))
    r = len(ech)
    base = [e for _, e in ech]
    # all nonzero vectors of the space, minimum-weight basis by greedy
    vecs = [0] * (1 << r)
    for k in range(r):
        h = 1 << k
        for i in range(h): vecs[h + i] = vecs[i] ^ base[k]
    order = sorted(range(1, 1 << r), key=lambda i: (vecs[i].bit_count(), vecs[i]))
    basis = []; bech = []
    for i in order:
        v = vecs[i]; w = v
        for pb, e in bech:
            if (w >> pb) & 1: w ^= e
        if w:
            bech.append((w.bit_length() - 1, w)); basis.append(v)
            if len(basis) == r: break
    # coordinates of each row in the chosen basis: solve via elimination with tracking
    track = []                            # (pivotbit, vec, combo over basis indices)
    for k, v in enumerate(basis):
        cmb = 1 << k
        for pb, e, ce in track:
            if (v >> pb) & 1: v ^= e; cmb ^= ce
        track.append((v.bit_length() - 1, v, cmb))
    lam = []                              # lam[j]: bitmask over basis indices with row_j = sum lam_jk basis_k
    for v in rows:
        cmb = 0
        for pb, e, ce in track:
            if (v >> pb) & 1: v ^= e; cmb ^= ce
        assert v == 0
        lam.append(cmb)
    s0 = sum(c << j for j, c in enumerate(cst))
    # column k of the map z -> s: bit j set iff lam[j] has bit k
    colz = [sum(((lam[j] >> k) & 1) << j for j in range(m)) for k in range(r)]
    sv = [0] * (1 << r); sv[0] = s0
    for k in range(r):
        h = 1 << k
        for i in range(h): sv[h + i] = sv[i] ^ colz[k]
    badz = {z for z in range(1 << r) if sv[z] in bad}
    return ('free', basis, badz)

def prime_implicants(points, r):
    """All prime implicants of the set (cubes as (care mask, value))."""
    full = (1 << r) - 1
    cur = {(full, p) for p in points}
    primes = set()
    while cur:
        nxt = set(); used = set()
        byk = {}
        for (mk, v) in cur: byk.setdefault(mk, set()).add(v)
        for mk, vals in byk.items():
            for v in vals:
                bits = mk
                while bits:
                    j = bits & -bits; bits ^= j
                    if v & j: continue
                    w = v | j
                    if w in vals:
                        nxt.add((mk & ~j, v)); used.add((mk, v)); used.add((mk, w))
        primes |= cur - used
        cur = nxt
    return primes

def cover(points, primes):
    left = set(points); out = []
    pl = list(primes)
    while left:
        best = max(pl, key=lambda c: (sum(1 for b in left if (b & c[0]) == c[1]), -c[0].bit_count()))
        out.append(best); left = {b for b in left if (b & best[0]) != best[1]}
    return out

class Enc:
    def __init__(self, nF):
        self.nv = nF; self.aux = {}; self.xors = []; self.clauses = []
    def var_of_mask(self, mask, nfix):
        if mask & (mask - 1) == 0:
            return mask.bit_length() - 1 - nfix + 1
        if mask not in self.aux:
            self.nv += 1; self.aux[mask] = self.nv
            self.xors.append((self.nv, mask))
        return self.aux[mask]

def encode(inst, asg, nfix, mode='prime', stats=None):
    N, NLEV, vstart, cons = inst
    fixmask = (1 << nfix) - 1
    asg &= fixmask
    nF = N - nfix
    E = Enc(nF)
    ndet = nfree = 0; dead = False
    pc_cache = {}
    for (lv, wt, m, fm, fc, bad) in cons:
        res = reduce_con(fm, fc, bad, fixmask, asg)
        if res[0] == 'det':
            ndet += 1
            if not res[1]: dead = True
            continue
        nfree += 1
        _, basis, badz = res
        r = len(basis)
        if not badz: continue
        if len(badz) == (1 << r): dead = True
        lits = [E.var_of_mask(b, nfix) for b in basis]
        if mode == 'direct':
            cubes = [((1 << r) - 1, z) for z in badz]
        else:
            key = (r, frozenset(badz))
            if key not in pc_cache:
                pr = prime_implicants(badz, r)
                pc_cache[key] = list(pr) if mode == 'allprime' else cover(badz, pr)
            cubes = pc_cache[key]
        for mk, val in cubes:
            cl = []
            for k in range(r):
                if (mk >> k) & 1:
                    cl.append(-lits[k] if (val >> k) & 1 else lits[k])
            E.clauses.append(cl)
    if stats is not None:
        stats.update(ndet=ndet, nfree=nfree, dead=dead, naux=len(E.xors), nclauses=len(E.clauses),
                     xorlen=sum(mk.bit_count() for _, mk in E.xors))
    return E

def write_xor_dimacs(E, nfix, fn):
    out = [f"p cnf {E.nv} {len(E.clauses) + len(E.xors)}"]
    for v, mk in E.xors:
        vs = [i - nfix + 1 for i in range(mk.bit_length()) if (mk >> i) & 1]
        out.append("x-" + str(v) + " " + " ".join(map(str, vs)) + " 0")      # v xor sum = 0
    for cl in E.clauses:
        out.append(" ".join(map(str, cl)) + " 0")
    open(fn, 'w').write("\n".join(out) + "\n")

def write_cnf(E, nfix, fn, chunk=3):
    """Pure CNF: aux = XOR of its base variables, as a chain of XORs of <= chunk inputs (direct encoding)."""
    nv = E.nv; cls = list(E.clauses)
    def xor_eq(t, ins):            # t = XOR(ins): all 2^k sign patterns of odd parity violation
        k = len(ins)
        allv = ins + [t]
        for bits in range(1 << (k + 1)):
            if bin(bits).count('1') % 2 == 1:       # forbid assignments with t != xor(ins): pattern parity odd
                cls.append([(-allv[q] if (bits >> q) & 1 else allv[q]) for q in range(k + 1)])
    for v, mk in E.xors:
        vs = [i - nfix + 1 for i in range(mk.bit_length()) if (mk >> i) & 1]
        cur = vs
        while len(cur) > chunk:
            nv += 1; xor_eq(nv, cur[:chunk]); cur = [nv] + cur[chunk:]
        xor_eq(v, cur)
    out = [f"p cnf {nv} {len(cls)}"] + [" ".join(map(str, c)) + " 0" for c in cls]
    open(fn, 'w').write("\n".join(out) + "\n")

if __name__ == '__main__':
    import argparse, time
    ap = argparse.ArgumentParser()
    ap.add_argument('inst'); ap.add_argument('asg'); ap.add_argument('nfix', type=int)
    ap.add_argument('--mode', default='prime'); ap.add_argument('--xor'); ap.add_argument('--cnf'); ap.add_argument('--chunk', type=int, default=3)
    a = ap.parse_args()
    t0 = time.time()
    inst = parse(a.inst)
    st = {}
    E = encode(inst, int(a.asg, 16), a.nfix, a.mode, st)
    t1 = time.time()
    if a.xor: write_xor_dimacs(E, a.nfix, a.xor)
    if a.cnf: write_cnf(E, a.nfix, a.cnf, a.chunk)
    print(f"ENC nfix {a.nfix} free {inst[0]-a.nfix} {st} enc_s {t1-t0:.2f} write_s {time.time()-t1:.2f}", flush=True)
