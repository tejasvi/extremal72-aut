"""Independent check of an instance augmented with derived ('projected', coset-death) constraints (audit code).
Inputs: ORIG (instance), DER (augmented instance) with DER.map (new index of every original constraint) and
DER.derived (per derived constraint k: source index, t, level, q, ...), DER.meta (derived rows '-1-k').
Checks
  O   every original constraint appears unchanged (level, weight, forms, constants, bad set) at its mapped index,
      the map is injective, originals keep their relative order, the file is sorted by level, every form uses no
      variable above its constraint's level, and the derived level equals the support level;
  A   for every derived constraint d with parent F and recorded t: there is a binary matrix Phi with d = Phi F exactly
      (masks and constants), and d uses no variable of a level > t (so Phi is in the left kernel of F restricted
      to the later levels);
  B   soundness, exact and independent of the choice of Phi: on the whole affine image of x -> (F(x), d(x)),
      every point with d(x) in Bad_d has F(x) in Bad_F (so d removes only nodes that F removes for every
      completion); and, when Phi is unique, the full-coset condition: Phi^-1(w) inside Bad_F for every w in Bad_d.
Usage: derchk.py ORIG DER"""
import sys, itertools, collections


def parse(fn):
    tok = open(fn).read().split(); p = 0
    N, NLEV, NC = int(tok[0]), int(tok[1]), int(tok[2]); p = 3
    vs = [int(t) for t in tok[p:p + NLEV + 1]]; p += NLEV + 1
    cons = []
    for _ in range(NC):
        lv, wt, m, nb = (int(tok[p + i]) for i in range(4)); p += 4
        forms = []
        for s in range(m): forms.append((int(tok[p], 16), int(tok[p + 1]))); p += 2
        bad = [int(t) for t in tok[p:p + nb]]; p += nb
        cons.append((lv, wt, forms, bad))
    assert p == len(tok)
    return N, NLEV, vs, cons


class GF2:
    def __init__(self): self.rows = {}
    def reduce(self, v, tag=0):
        for b, (r, t) in self.rows.items():
            if (v >> b) & 1: v ^= r; tag ^= t
        return v, tag
    def add(self, v, tag=0):
        v, tag = self.reduce(v, tag)
        if v == 0: return False, tag
        b = v.bit_length() - 1
        for b2, (r, t) in list(self.rows.items()):
            if (r >> b) & 1: self.rows[b2] = (r ^ v, t ^ tag)
        self.rows[b] = (v, tag)
        return True, tag


def fail(msg):
    print('FAIL', msg, flush=True); sys.exit(2)


def main():
    orig, der = sys.argv[1], sys.argv[2]
    N, NL, vs, oc = parse(orig)
    N2, NL2, vs2, dc = parse(der)
    if (N, NL, vs) != (N2, NL2, vs2): fail('header')
    levof = [0] * N
    for t in range(NL):
        for v in range(vs[t], vs[t + 1]): levof[v] = t
    omap = list(map(int, open(der + '.map').read().split()))
    if len(omap) != len(oc) or len(set(omap)) != len(omap): fail('map')
    if omap != sorted(omap): fail('originals reordered')
    for i, j in enumerate(omap):
        if dc[j] != oc[i]: fail(f'original {i} changed at {j}')
    if any(dc[k][0] > dc[k + 1][0] for k in range(len(dc) - 1)): fail('not sorted by level')
    for k, (lv, wt, forms, bad) in enumerate(dc):
        sup = 0
        for f, c in forms: sup |= f
        if sup >> vs[lv + 1]: fail(f'constraint {k} uses a variable above its level')
    meta = [l.split() for l in open(der + '.meta').read().rstrip('\n').split('\n')]
    if len(meta) != len(dc): fail('meta length')
    info = [list(map(int, l.split())) for l in open(der + '.derived').read().split('\n') if l.strip()]
    isorig = set(omap)
    nder = 0; stats = collections.Counter(); uniq = 0; coset_checked = 0; pts = 0
    seen_k = set()
    for j, (lv, wt, d, badd) in enumerate(dc):
        if j in isorig: continue
        nder += 1
        if len(meta[j]) != 1 or int(meta[j][0]) >= 0: fail(f'derived {j} meta')
        k = -1 - int(meta[j][0])
        if k in seen_k: fail('derived meta index repeated')
        seen_k.add(k)
        src, t, dl, q = info[k][:4]
        if dl != lv or len(d) != q: fail(f'derived {j} level/q')
        sup = 0
        for f, c in d: sup |= f
        if (levof[sup.bit_length() - 1] if sup else 0) != lv: fail(f'derived {j} level != support level')
        if sup >> vs[t + 1]: fail(f'derived {j} uses a variable of a level > t = {t}')
        plv, pwt, F, badF = oc[src]
        if lv >= plv: fail(f'derived {j} not below its parent')
        m = len(F)
        # A: d_k = sum phi_ks F_s (affine vectors: mask | const << N)
        B = GF2()
        for s, (f, c) in enumerate(F): B.add(f | (c << N), 1 << s)
        rankF = len(B.rows)
        Phi = []
        for (f, c) in d:
            rem, tag = B.reduce(f | (c << N), 0)
            if rem: fail(f'derived {j}: form not in the span of the parent forms')
            Phi.append(tag)
        if rankF == m: uniq += 1
        # B: exact soundness on the joint affine image of x -> (F(x), d(x))
        cF = sum(c << s for s, (f, c) in enumerate(F)); cd = sum(c << s for s, (f, c) in enumerate(d))
        J = GF2()
        for v in range(N):
            col = sum(((f >> v) & 1) << s for s, (f, c) in enumerate(F))
            col |= sum(((f >> v) & 1) << s for s, (f, c) in enumerate(d)) << m
            if col: J.add(col)
        basis = [r for r, t2 in J.rows.values()]
        if len(basis) > 20: fail(f'derived {j}: joint image too large')
        bF = set(badF); bD = set(badd)
        if any(not (0 <= w < (1 << q)) for w in bD): fail(f'derived {j}: bad value out of range')
        cur = cF | (cd << m); mF = (1 << m) - 1
        for z in range(1 << len(basis)):
            if z: cur ^= basis[(z & -z).bit_length() - 1]
            if (cur >> m) in bD and (cur & mF) not in bF: fail(f'derived {j}: reachable parent-good syndrome inside a derived bad value')
        pts += 1 << len(basis)
        # full-coset condition with Phi (exact when Phi is unique)
        if rankF == m:
            for s in range(1 << m):
                w = 0
                for i in range(q): w |= ((Phi[i] & s).bit_count() & 1) << i
                if w in bD and s not in bF: fail(f'derived {j}: coset of w={w} not inside the parent bad set')
            coset_checked += 1
        stats[lv] += 1
    if len(seen_k) != len(info): fail('derived lines without a constraint')
    print(f'O ok: {len(oc)} originals unchanged at mapped indices; A ok and B ok for {nder} derived constraints '
          f'(levels {dict(sorted(stats.items()))}); joint-image points checked {pts}; Phi unique for {uniq}, '
          f'full-coset condition checked for {coset_checked}', flush=True)
    print('RESULT PASS', der, flush=True)


if __name__ == '__main__':
    main()
