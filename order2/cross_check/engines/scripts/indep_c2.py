"""Independent semantic check of a plain-C2 package (inst.txt, inst.txt.meta, inst.txt.pkl, flag.txt), audit code.
Shares no code with the builder (mkinst.py / prep_code.py); own GF(2) routines and own parser of codes36.txt.
Checks
  P1  Y = code CI of codes36.txt is self-dual [36,18,8] and contains 1; flag = pickle basis w, a basis of Y
  P3  every parametrised Gram matrix satisfies G_kk + B(w_k,1) = |w_k|/2 (identity of affine forms)
  P4  injective (rank N); free entries are unit forms; entry (i,j), i<=j, uses only variables of rows <= i
  P5  completeness modulo gauge: Gamma = span{D_p, p = 0..35} (rank 35), Gamma and Lin(P) inside S0 (homogeneous
      diagonal equations), Lin(P) cap Gamma = 0, N + rank Gamma = dim S0
  C1  file vs meta, per constraint (y, ub): y in Y of weight 8/10/12; ub a basis of S_y = {u in Y: u & y = 0};
      the m affine forms equal B(y, ub_s) exactly; the bad set equals the set of syndromes (z.ub_s)_s of all
      patterns z outside y with |z| < (16-|y|)/2 (exact set equality); level = support level
  C2  every word of weight 8, 10, 12 of Y has exactly one constraint; no other constraint
  C3  every word of weight 14 is vacuous: the syndrome 0 (the only bad one) is not in the affine image
Usage: indep_c2.py PKGDIR CI"""
import sys, os, pickle, itertools, time, collections

M = 36; K = 18; DMIN = 16; ALL = (1 << M) - 1
CODES = '<HOME>/c72/c2/codes36.txt'


class GF2:
    """Fully reduced row basis, pivot = highest bit, with tag (transform) tracking."""
    def __init__(self):
        self.rows = {}
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
    def rank(self): return len(self.rows)


def fail(msg):
    print('FAIL', msg, flush=True); sys.exit(2)


def load_codes(path):
    txt = open(path).read().strip()
    codes = []
    for block in txt.split('\n\n'):
        rows = [l.strip() for l in block.split('\n') if l.strip()]
        code = []
        for r in rows:
            assert len(r) == M and set(r) <= {'0', '1'}
            code.append(sum(1 << j for j, ch in enumerate(r) if ch == '1'))
        codes.append(code)
    return codes


def parse_instance(fn):
    with open(fn) as f:
        N, NLEV, NC = map(int, f.readline().split())
        vs = list(map(int, f.readline().split()))
        cons = []
        for c in range(NC):
            lv, wt, m, nb = map(int, f.readline().split())
            forms = []
            for s in range(m):
                hx, cc = f.readline().split(); forms.append((int(hx, 16), int(cc)))
            bad = list(map(int, f.readline().split()))
            assert len(bad) == nb, (c, nb, len(bad))
            cons.append((lv, wt, forms, bad))
        rest = f.read().strip()
        assert rest == '', 'trailing data'
    return N, NLEV, vs, cons


def main():
    pkg, ci = sys.argv[1], int(sys.argv[2])
    t0 = time.time()
    codes = load_codes(CODES)
    if len(codes) != 41: fail('number of codes')
    Ygen = codes[ci]
    # ---- P1
    Yall = [0]
    for g in Ygen: Yall = Yall + [s ^ g for s in Yall]
    Yset = set(Yall)
    if len(Yset) != 1 << K: fail('|Y|')
    if any(((a & b).bit_count() & 1) for a in Ygen for b in Ygen): fail('Y not self-orthogonal')
    if ALL not in Yset: fail('1 not in Y')
    wd = collections.Counter(y.bit_count() for y in Yall)
    if min(k for k in wd if k) != 8: fail('d(Y) != 8')
    flag = [int(x) for x in open(os.path.join(pkg, 'flag.txt')).read().split()[1:]]
    P = pickle.load(open(os.path.join(pkg, 'inst.txt.pkl'), 'rb'))
    w, free, entf, N, E = P['w'], P['free'], P['entf'], P['N'], P['E']
    if list(w) != flag: fail('pickle basis != flag')
    if len(w) != K or any(x not in Yset for x in w): fail('flag not in Y')
    WB = GF2()
    for k, x in enumerate(w):
        ok, _ = WB.add(x, 1 << k)
        if not ok: fail('flag dependent')
    def coords(x):
        v, t = WB.reduce(x, 0)
        if v: fail('coords')
        return t
    Emine = [(i, j) for i in range(K) for j in range(i, K)]
    if list(map(tuple, E)) != Emine: fail('entry order')
    eidx = {e: n for n, e in enumerate(Emine)}; NE = len(Emine)
    if len(entf) != NE: fail('entf length')
    if any(vm >> N for vm, c in entf): fail('entf uses variable >= N')
    aff = [vm | (c << N) for (vm, c) in entf]
    Gaff = [[aff[eidx[(min(a, b), max(a, b))]] for b in range(K)] for a in range(K)]
    def Bform(cx, cz):
        f = 0
        for a in range(K):
            if (cx >> a) & 1:
                for b in range(K):
                    if (cz >> b) & 1: f ^= Gaff[a][b]
        return f
    def Bmask(cx, cz):
        mm = 0
        for a in range(K):
            if (cx >> a) & 1:
                for b in range(K):
                    if (cz >> b) & 1: mm ^= 1 << eidx[(min(a, b), max(a, b))]
        return mm
    c1 = coords(ALL)
    # ---- P3
    for k in range(K):
        if Gaff[k][k] ^ Bform(1 << k, c1) != (((w[k].bit_count() // 2) & 1) << N): fail(f'P3 diagonal at {k}')
    # ---- P4
    level = [Emine[e][0] for e in free]
    if len(free) != N or sorted(free) != list(free): fail('free list')
    for n, e in enumerate(free):
        if aff[e] != (1 << n): fail('free entry form')
    for e in range(NE):
        vm = aff[e] & ((1 << N) - 1)
        if vm and level[vm.bit_length() - 1] > Emine[e][0]: fail(f'P4 entry {Emine[e]}')
    R = GF2()
    for e in range(NE): R.add(aff[e] & ((1 << N) - 1))
    if R.rank() != N: fail('P4 rank')
    # ---- P5
    eqs = [(1 << eidx[(k, k)]) ^ Bmask(1 << k, c1) for k in range(K)]
    EQ = GF2()
    for q in eqs: EQ.add(q)
    dimS0 = NE - EQ.rank()
    def in_S0(vec): return all(((q & vec).bit_count() & 1) == 0 for q in eqs)
    gam = []
    for p in range(M):
        v = 0
        for (i, j) in Emine:
            if ((w[i] & w[j]) >> p) & 1: v |= 1 << eidx[(i, j)]
        gam.append(v)
    if not all(in_S0(g) for g in gam): fail('P5 gauge not in S0')
    GB = GF2()
    for g in gam: GB.add(g)
    rg = GB.rank()
    cols = []
    for v in range(N):
        cv = 0
        for e in range(NE):
            if (aff[e] >> v) & 1: cv |= 1 << e
        cols.append(cv)
    if not all(in_S0(cv) for cv in cols): fail('P5 column not in S0')
    LB = GF2()
    for cv in cols: LB.add(cv)
    for g in gam: LB.add(g)
    if LB.rank() != N + rg: fail('P5 Lin(P) meets Gamma')
    if N + rg != dimS0: fail(f'P5 N {N} + rank Gamma {rg} != dim S0 {dimS0}')
    print(f'P1-P5 ok: code {ci} weights {dict(sorted(wd.items()))}; N {N}, rank Gamma {rg}, dim S0 {dimS0}', flush=True)
    # ---- file and meta
    Nf, NLEV, vs, cons = parse_instance(os.path.join(pkg, 'inst.txt'))
    if Nf != N or NLEV != K: fail('header')
    vs2 = [0] * (K + 1)
    for t in range(K): vs2[t + 1] = vs2[t] + sum(1 for v in range(N) if level[v] == t)
    if vs != vs2: fail('vstart')
    if any(cons[i][0] > cons[i + 1][0] for i in range(len(cons) - 1)): fail('not sorted by level')
    meta = [list(map(int, l.split())) for l in open(os.path.join(pkg, 'inst.txt.meta')) if l.strip()]
    if len(meta) != len(cons): fail('meta length')
    def yrow_forms(y):
        cy = coords(y)
        yrow = []
        for b in range(K):
            f = 0
            for a in range(K):
                if (cy >> a) & 1: f ^= Gaff[a][b]
            yrow.append(f)
        return yrow
    def form_of(yrow, u):
        cu = coords(u); f = 0
        for b in range(K):
            if (cu >> b) & 1: f ^= yrow[b]
        return f
    def short_dim(y):
        B = GF2()
        for x in w: B.add(x & y)
        return K - B.rank()
    seen = collections.Counter(); stats = collections.Counter()
    for idx, ((lv, wt, forms, bad), mrow) in enumerate(zip(cons, meta)):
        y, ub = mrow[0], mrow[1:]
        if y not in Yset or y.bit_count() != wt or wt not in (8, 10, 12): fail(f'C1 word {idx}')
        seen[y] += 1
        m = len(ub)
        if m != len(forms): fail(f'C1 m {idx}')
        UB = GF2()
        for u in ub:
            if u not in Yset or (u & y): fail(f'C1 ub not in S_y {idx}')
            ok, _ = UB.add(u)
            if not ok: fail(f'C1 ub dependent {idx}')
        if m != short_dim(y): fail(f'C1 ub not a basis {idx}')
        yrow = yrow_forms(y)
        for s, u in enumerate(ub):
            f = form_of(yrow, u)
            if (f & ((1 << N) - 1), f >> N) != forms[s]: fail(f'C1 form {idx}.{s}')
        r = (DMIN - wt) // 2
        cpos = [p for p in range(M) if not (y >> p) & 1]
        colp = {p: sum(((u >> p) & 1) << s for s, u in enumerate(ub)) for p in cpos}
        mybad = set()
        for k in range(r):
            for sub in itertools.combinations(cpos, k):
                s = 0
                for p in sub: s ^= colp[p]
                mybad.add(s)
        if set(bad) != mybad or len(set(bad)) != len(bad): fail(f'C1 bad set {idx}')
        sup = 0
        for (vm, c) in forms: sup |= vm
        if (level[sup.bit_length() - 1] if sup else 0) != lv: fail(f'C1 level {idx}')
        stats[wt] += 1
    low = [y for y in Yall if y.bit_count() in (8, 10, 12)]
    if set(seen) != set(low) or any(v != 1 for v in seen.values()): fail('C2 coverage')
    print(f'C1/C2 ok: {len(cons)} constraints = all words of weight 8/10/12 {dict(sorted(stats.items()))}', flush=True)
    # ---- C3 weight 14 vacuous
    n14 = 0
    for y in Yall:
        if y.bit_count() != 14: continue
        KB = GF2(); ker = []
        for k in range(K):
            ok, tag = KB.add(w[k] & y, 1 << k)
            if not ok: ker.append(tag)
        yrow = yrow_forms(y)
        fs = []
        for tag in ker:
            f = 0
            for b in range(K):
                if (tag >> b) & 1: f ^= yrow[b]
            fs.append(f)
        c0 = sum(((f >> N) & 1) << s for s, f in enumerate(fs))
        span = GF2()
        for v in range(N):
            col = sum(((f >> v) & 1) << s for s, f in enumerate(fs))
            if col: span.add(col)
        if span.reduce(c0)[0] == 0: fail(f'C3 weight-14 word {y:x} can reach syndrome 0')
        n14 += 1
    print(f'C3 ok: {n14} words of weight 14, none can reach its bad syndrome', flush=True)
    print('RESULT PASS', os.path.basename(os.path.normpath(pkg)), f'time {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
