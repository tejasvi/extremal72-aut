"""End-to-end check of an instance file against genuine codes.
For assignments X (random, or read from a file of hex assignments): build the length-72 code C(X) from the
parametrised Gram matrix (rows (w_k|w_k) and (x_k|x_k+w_k), <x_k, w_j> = G_kj), verify it is self-dual, doubly even
and invariant under alpha (swap halves) and beta (bb on both halves); enumerate ALL words of weight <= 14 with the
Brouwer-Zimmermann program lowwords; then compare, constraint by constraint, 'file constraint violated at X'
with 'C(X) has a word of weight < 16 whose pair-sum y lies in the constraint's beta-orbit' (orbit map from
indep_check).  Optionally (--gauge) also compare the low-weight distribution of C(X) and C(X + g) for random gauge
vectors g (D_R for beta-closed pair sets and D_T).
Usage: e2e.py CI RI INSTANCE PICKLE MAP NRAND SEED [--gauge] [--xfile FILE]"""
import sys, pickle, random, subprocess, collections, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE + '/../../../model')
sys.path.insert(0, HERE + '/../scripts')
from autinv import load
from indep_check import GF2, parse_instance, apply_perm
LOWW = HERE + '/../scripts/lowwords'
M = 36; K = 18; A36 = (1 << M) - 1


def par(x): return x.bit_count() & 1


def main():
    ci, ri, instf, pklf, mapf, nrand, seed = sys.argv[1:8]
    ci, ri, nrand, seed = int(ci), int(ri), int(nrand), int(seed)
    gauge = '--gauge' in sys.argv
    xs = []
    if '--xfile' in sys.argv:
        xs = [int(l.split()[0], 16) for l in open(sys.argv[sys.argv.index('--xfile') + 1]) if l.strip()]
    codes = load(); Ygen = codes[ci]
    P = pickle.load(open(pklf, 'rb')); w, free, entf, N = P['w'], P['free'], P['entf'], P['N']
    MP = pickle.load(open(mapf, 'rb')); beta = MP['beta']; cmap = MP['cmap']
    assert MP['ci'] == ci and MP['ri'] == ri
    Nf, NLEV, vs, cons = parse_instance(instf); assert Nf == N
    E = [(i, j) for i in range(K) for j in range(i, K)]; eidx = {e: n for n, e in enumerate(E)}
    # dual basis d_j: <w_i, d_j> = delta_ij
    WB = GF2()
    for k in range(K): WB.add(w[k], 1 << k)
    d = [0] * K
    for b, (r, tag) in WB.rows.items():
        for j in range(K):
            if (tag >> j) & 1: d[j] |= 1 << b
    for i in range(K):
        for j in range(K): assert par(w[i] & d[j]) == (i == j)
    # gauge vectors in entry space
    orbs = sorted({(min(p, beta[p]), max(p, beta[p])) for p in range(M)})
    def Dvec(R):
        v = 0
        for (i, j) in E:
            if (w[i] & w[j] & R).bit_count() & 1: v |= 1 << eidx[(i, j)]
        return v
    gam = [Dvec((1 << p) | (1 << q)) for (p, q) in orbs]
    T = 0
    for (p, q) in orbs: T |= 1 << p
    gam.append(Dvec(T))
    rnd = random.Random(seed)

    def gram_vec(X):   # entry-space vector of G(X)
        v = 0
        for e, (vm, c) in enumerate(entf):
            if par(vm & X) ^ c: v |= 1 << e
        return v

    def code_rows(gv):
        G = [[(gv >> eidx[(min(a, b), max(a, b))]) & 1 for b in range(K)] for a in range(K)]
        rows = []
        for k in range(K): rows.append(w[k] | (w[k] << M))
        for a in range(K):
            x = 0
            for j in range(K):
                if G[a][j]: x ^= d[j]
            for j in range(K): assert par(x & w[j]) == G[a][j]
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
            sw = v | (u << M)
            assert B.reduce(sw)[0] == 0, 'alpha'
            bu = apply_perm(beta, u); bv = apply_perm(beta, v)
            assert B.reduce(bu | (bv << M))[0] == 0, 'beta'
        return B

    def lowwords(rows):
        inp = '\n'.join(f'{r >> 64:x} {r & ((1 << 64) - 1):x}' for r in rows) + '\n'
        out = subprocess.run([LOWW, '14'], input=inp, capture_output=True, text=True).stdout
        words = []
        for l in out.split('\n'):
            if l.startswith('W '):
                f = l.split(); words.append(((int(f[1], 16) << 64) | int(f[2], 16), int(f[3])))
            elif l.startswith('COUNT'): cnt = int(l.split()[1])
        assert len(words) == cnt
        return words

    badsets = [set(bad) for (lv, wt, forms, bad) in cons]
    tot = collections.Counter()
    todo = xs + [rnd.getrandbits(N) for _ in range(nrand)]
    for X in todo:
        gv = gram_vec(X)
        rows = code_rows(gv)
        B = check_code(rows)
        words = lowwords(rows)
        for c, wtc in words:
            assert B.reduce(c)[0] == 0, 'low word not in code'
            assert wtc == c.bit_count()
        wd = collections.Counter(wtc for c, wtc in words)
        tot['codes'] += 1
        if any(k % 4 for k in wd): tot['NOT_DOUBLY_EVEN'] += 1
        hit = set(((c & A36) ^ (c >> M)) for c, wtc in words)
        assert 0 not in hit, 'weight <16 word with y = 0'
        # file predicates
        viol = []
        for idx, (lv, wt, forms, bad) in enumerate(cons):
            s = 0
            for k, (vm, cc) in enumerate(forms): s |= (par(vm & X) ^ cc) << k
            viol.append(s in badsets[idx])
        for idx, v in enumerate(viol):
            if v: tot[f'viol_wt{cons[idx][1]}'] += 1
        covered = set()
        for idx, ys in cmap.items():
            h = any(y in hit for y in ys)
            covered.update(ys)
            if viol[idx] and h: tot['viol&witness'] += 1
            elif viol[idx] and not h: tot['VIOL_NO_WITNESS'] += 1
            elif h and not viol[idx]: tot['WITNESS_NOT_VIOL'] += 1
            else: tot['ok_both_clear'] += 1
        if not hit <= covered: tot['HIT_Y_NOT_COVERED'] += 1
        tot['lowwords'] += len(words)
        if gauge:
            for _ in range(2):
                g = 0
                for gg in gam:
                    if rnd.getrandbits(1): g ^= gg
                rows2 = code_rows(gv ^ g)
                check_code(rows2)
                wd2 = collections.Counter(wtc for c, wtc in lowwords(rows2))
                tot['gauge_same' if wd2 == wd else 'GAUGE_DIFFERENT'] += 1
        print('X', f'{X:x}', 'lowwords', dict(sorted(wd.items())), 'violated', sum(viol), flush=True)
    print('TOTALS', dict(tot), flush=True)
    bad = tot['VIOL_NO_WITNESS'] + tot['WITNESS_NOT_VIOL'] + tot['HIT_Y_NOT_COVERED'] + tot['GAUGE_DIFFERENT'] + tot['NOT_DOUBLY_EVEN']
    print('RESULT', 'PASS' if bad == 0 else 'FAIL', f'{ci}_{ri}', flush=True)


if __name__ == '__main__':
    main()
