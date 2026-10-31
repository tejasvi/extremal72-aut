"""End-to-end check of a plain-C2 package against genuine codes (audit code).
For random assignments X: build the length-72 code C(X) from the parametrised Gram matrix (rows (w_k|w_k) and
(x_k|x_k+w_k) with <x_k, w_j> = G_kj), check it is self-dual, doubly even and sigma-invariant (sigma = swap of the
two halves), enumerate ALL its words of weight <= 14 (Brouwer-Zimmermann, lowwords), and compare per constraint:
'file constraint violated at X' <=> 'C(X) has a word of weight < 16 over the constraint's word y' (y from meta).
Identifications: for random gauge vectors g (sums of D_p) the code of G + g must be the image of C(X) under the
swap of the pairs p in g; for elements h of Aut(Y) (generator products) the code of B^h(x,y) = B(hx,hy) must be the
image of C(X) under the pair-preserving lift (u|v) -> (h^-1 u | h^-1 v) ... checked as equality of codes.
Usage: e2e_c2.py PKGDIR CI NRAND SEED"""
import sys, os, pickle, random, subprocess, collections
sys.path.insert(0, '<HOME>/c72/audit/c2audit/engine-check/scripts')
from indep_c2 import GF2, load_codes, parse_instance, CODES
M = 36; K = 18; A36 = (1 << M) - 1
LOWW = '<HOME>/c72/audit/c2audit/engine-check/scripts/lowwords'
INVS = '<HOME>/c72/c2par/invs.pkl'


def par(x): return x.bit_count() & 1


def ap(p, x):
    o = 0
    while x:
        lb = x & -x; i = lb.bit_length() - 1; o |= 1 << p[i]; x ^= lb
    return o


def main():
    pkg, ci, nrand, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rnd = random.Random(seed)
    codes = load_codes(CODES); Ygen = codes[ci]
    P = pickle.load(open(os.path.join(pkg, 'inst.txt.pkl'), 'rb')); w, free, entf, N = P['w'], P['free'], P['entf'], P['N']
    Nf, NLEV, vs, cons = parse_instance(os.path.join(pkg, 'inst.txt')); assert Nf == N
    meta = [list(map(int, l.split())) for l in open(os.path.join(pkg, 'inst.txt.meta')) if l.strip()]
    badsets = [set(c[3]) for c in cons]
    E = [(i, j) for i in range(K) for j in range(i, K)]; eidx = {e: n for n, e in enumerate(E)}
    WB = GF2()
    for k in range(K): WB.add(w[k], 1 << k)
    d = [0] * K
    for b, (r, tag) in WB.rows.items():
        for j in range(K):
            if (tag >> j) & 1: d[j] |= 1 << b
    for i in range(K):
        for j in range(K): assert par(w[i] & d[j]) == (i == j)
    def coords(x):
        v, t = WB.reduce(x, 0); assert v == 0; return t
    gens = pickle.load(open(INVS, 'rb'))[ci]['perms']
    Yset = None

    def gram_from_X(X):
        G = [[0] * K for _ in range(K)]
        for e, (vm, c) in enumerate(entf):
            i, j = E[e]; G[i][j] = G[j][i] = par(vm & X) ^ c
        return G

    def code_rows(G):
        rows = [w[k] | (w[k] << M) for k in range(K)]
        for a in range(K):
            x = 0
            for j in range(K):
                if G[a][j]: x ^= d[j]
            rows.append(x | ((x ^ w[a]) << M))
        return rows

    def check_code(rows):
        B = GF2()
        for r in rows: B.add(r)
        assert B.rank() == 36, 'rank'
        assert all(r.bit_count() % 4 == 0 for r in rows), 'doubly even'
        assert all(par(r1 & r2) == 0 for r1 in rows for r2 in rows), 'self-orthogonal'
        for r in rows:
            u = r & A36; v = r >> M
            assert B.reduce(v | (u << M))[0] == 0, 'sigma'
        return B

    def lowwords(rows):
        inp = '\n'.join(f'{r >> 64:x} {r & ((1 << 64) - 1):x}' for r in rows) + '\n'
        out = subprocess.run([LOWW, '14'], input=inp, capture_output=True, text=True).stdout
        words = []; cnt = -1
        for l in out.split('\n'):
            if l.startswith('W '):
                f = l.split(); words.append((int(f[1], 16) << 64) | int(f[2], 16))
            elif l.startswith('COUNT'): cnt = int(l.split()[1])
        assert len(words) == cnt
        return words

    def same_code(B1, rows2):
        return all(B1.reduce(r)[0] == 0 for r in rows2)

    tot = collections.Counter()
    for it in range(nrand):
        X = rnd.getrandbits(N)
        G = gram_from_X(X); rows = code_rows(G); B = check_code(rows)
        words = lowwords(rows)
        for c in words: assert B.reduce(c)[0] == 0
        wdist = collections.Counter(c.bit_count() for c in words)
        if any(k % 4 for k in wdist): tot['NOT_DOUBLY_EVEN'] += 1
        hit = set((c & A36) ^ (c >> M) for c in words)
        if 0 in hit: tot['Y_ZERO_LOW_WORD'] += 1
        hitw = collections.Counter(y.bit_count() for y in hit)
        for wt in hitw:
            if wt not in (8, 10, 12): tot[f'LOW_WORD_OVER_WEIGHT_{wt}'] += 1
        for idx, (lv, wt, forms, bad) in enumerate(cons):
            s = 0
            for k2, (vm, cc) in enumerate(forms): s |= (par(vm & X) ^ cc) << k2
            v = s in badsets[idx]; h = meta[idx][0] in hit
            if v and h: tot['viol&word'] += 1
            elif v: tot['VIOL_NO_WORD'] += 1
            elif h: tot['WORD_NOT_VIOL'] += 1
            else: tot['clear'] += 1
        tot['codes'] += 1; tot['lowwords'] += len(words)
        # gauge: G + D_S  <->  swap of the pairs in S
        S = rnd.getrandbits(M)
        G2 = [[G[i][j] ^ ((w[i] & w[j] & S).bit_count() & 1) for j in range(K)] for i in range(K)]
        rows2 = code_rows(G2)
        swapped = []
        for r in rows:
            u = r & A36; v = r >> M
            u2 = (u & ~S) | (v & S); v2 = (v & ~S) | (u & S)
            swapped.append(u2 | (v2 << M))
        BS = GF2()
        for r in swapped: BS.add(r)
        tot['gauge_equal' if same_code(BS, rows2) else 'GAUGE_NOT_EQUAL'] += 1
        # Aut(Y): B^h(x,y) = B(hx,hy)  <->  C_{B^h} = lift(h^-1)(C_B)
        h = list(range(M))
        for _ in range(rnd.randint(1, 5)):
            g = rnd.choice(gens); h = [g[h[p]] for p in range(M)]
        hw = [coords(ap(h, w[k])) for k in range(K)]
        G3 = [[0] * K for _ in range(K)]
        for i in range(K):
            for j in range(K):
                s = 0
                for a in range(K):
                    if (hw[i] >> a) & 1:
                        for b in range(K):
                            if (hw[j] >> b) & 1: s ^= G[a][b]
                G3[i][j] = s
        rows3 = code_rows(G3)
        hinv = [0] * M
        for p in range(M): hinv[h[p]] = p
        lifted = [ap(hinv, r & A36) | (ap(hinv, r >> M) << M) for r in rows]
        BL = GF2()
        for r in lifted: BL.add(r)
        tot['aut_equal' if same_code(BL, rows3) else 'AUT_NOT_EQUAL'] += 1
    bad = sum(v for k, v in tot.items() if k.isupper() or k[0].isupper())
    print('TOTALS', dict(tot), flush=True)
    print('RESULT', 'PASS' if bad == 0 else 'FAIL', os.path.basename(os.path.normpath(pkg)), flush=True)


if __name__ == '__main__':
    main()
