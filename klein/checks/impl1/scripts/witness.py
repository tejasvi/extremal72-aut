"""Kill witnesses.  Input: KILL records 'KILL t PREFIXHEX v' from lwe_kill (a child v of level t removed by lwe below
the prefix).  For every record: (1) re-evaluate independently which level-t file constraints the child violates
(must be >= 1, else lwe removed a child wrongly); (2) take the first violated constraint, its beta-orbit of words y
(map from indep_check); (3) for NCOMP random completions X of all variables of levels > t build the genuine code
C(X) (self-dual, doubly even, alpha- and beta-invariant: checked) and exhibit an explicit codeword
(x | x + y), x in phi(y) + Y, of weight |y| + 2|x outside y| < 16, verified to lie in C(X).
Usage: witness.py CI RI INSTANCE PICKLE MAP KILLFILE NCOMP SEED"""
import sys, pickle, random, itertools, collections, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE + '/../../../model')
sys.path.insert(0, HERE + '/../scripts')
from autinv import load
from indep_check import GF2, parse_instance, apply_perm
M = 36; K = 18; A36 = (1 << M) - 1


def par(x): return x.bit_count() & 1


def main():
    ci, ri, instf, pklf, mapf, killf, ncomp, seed = sys.argv[1:9]
    ci, ri, ncomp, seed = int(ci), int(ri), int(ncomp), int(seed)
    P = pickle.load(open(pklf, 'rb')); w, free, entf, N = P['w'], P['free'], P['entf'], P['N']
    MP = pickle.load(open(mapf, 'rb')); beta = MP['beta']; cmap = MP['cmap']
    Nf, NLEV, vs, cons = parse_instance(instf); assert Nf == N
    bylev = collections.defaultdict(list)
    for idx, c in enumerate(cons): bylev[c[0]].append(idx)
    badsets = [set(c[3]) for c in cons]
    E = [(i, j) for i in range(K) for j in range(i, K)]; eidx = {e: n for n, e in enumerate(E)}
    WB = GF2()
    for k in range(K): WB.add(w[k], 1 << k)
    d = [0] * K
    for b, (r, tag) in WB.rows.items():
        for j in range(K):
            if (tag >> j) & 1: d[j] |= 1 << b
    def coords(x):
        v, t = WB.reduce(x, 0); assert v == 0; return t
    rnd = random.Random(seed)
    recs = []
    for l in open(killf):
        if l.startswith('KILL '):
            f = l.split(); recs.append((int(f[1]), int(f[2], 16), int(f[3])))
    st = collections.Counter(); wdist = collections.Counter(); per_level = collections.Counter(); per_wt = collections.Counter()
    puncache = {}
    for (t, pre, v) in recs:
        asg = pre | (v << vs[t])
        assert pre >> vs[t] == 0
        viol = []
        for idx in bylev[t]:
            lv, wt, forms, bad = cons[idx]
            s = 0
            for k, (vm, cc) in enumerate(forms): s |= (par(vm & asg) ^ cc) << k
            if s in badsets[idx]: viol.append(idx)
        if not viol:
            st['ENGINE_KILLED_WITHOUT_VIOLATION'] += 1
            print('ENGINE BUG? no violated constraint for', t, hex(pre), v, flush=True); continue
        st['records'] += 1; per_level[t] += 1
        idx = viol[0]; ys = cmap[idx]; wt = cons[idx][1]; per_wt[wt] += 1
        for _ in range(ncomp):
            X = asg | (rnd.getrandbits(N - vs[t + 1]) << vs[t + 1]) if vs[t + 1] < N else asg
            G = [[0] * K for _ in range(K)]
            for e, (vm, c) in enumerate(entf):
                i, j = E[e]; G[i][j] = G[j][i] = par(vm & X) ^ c
            xs = []
            for a in range(K):
                x = 0
                for j in range(K):
                    if G[a][j]: x ^= d[j]
                xs.append(x)
            rows = [w[k] | (w[k] << M) for k in range(K)] + [xs[a] | ((xs[a] ^ w[a]) << M) for a in range(K)]
            B = GF2()
            for r in rows: B.add(r)
            assert B.rank() == 36 and all(r.bit_count() % 4 == 0 for r in rows)
            assert all(par(r1 & r2) == 0 for r1 in rows for r2 in rows)
            for r in rows:
                u = r & A36; vv = r >> M
                assert B.reduce(vv | (u << M))[0] == 0 and B.reduce(apply_perm(beta, u) | (apply_perm(beta, vv) << M))[0] == 0
            found = None
            for y in ys:
                wy = y.bit_count(); rr = (16 - wy) // 2
                cy = coords(y); xy = 0
                for a in range(K):
                    if (cy >> a) & 1: xy ^= xs[a]
                if y not in puncache:
                    PB = GF2()
                    for k in range(K): PB.add(w[k] & ~y & A36, 1 << k)
                    puncache[y] = PB
                PB = puncache[y]
                cpos = [p for p in range(M) if not (y >> p) & 1]
                for kk in range(rr):
                    for sub in itertools.combinations(cpos, kk):
                        z = 0
                        for p in sub: z |= 1 << p
                        rem, tag = PB.reduce((xy ^ z) & ~y & A36, 0)
                        if rem == 0:
                            f = 0
                            for k in range(K):
                                if (tag >> k) & 1: f ^= w[k]
                            x = xy ^ f
                            c = x | ((x ^ y) << M)
                            if B.reduce(c)[0] == 0 and c.bit_count() < 16 and c.bit_count() == wy + 2 * kk:
                                found = c; break
                    if found: break
                if found: break
            if found:
                st['witnessed'] += 1; wdist[found.bit_count()] += 1
            else:
                st['NO_WITNESS'] += 1
                print('NO WITNESS', t, hex(pre), v, idx, flush=True)
    print('per level', dict(sorted(per_level.items())), 'per constraint weight', dict(sorted(per_wt.items())), flush=True)
    print('witness weights', dict(sorted(wdist.items())), flush=True)
    print('TOTALS', dict(st), flush=True)
    bad = st['ENGINE_KILLED_WITHOUT_VIOLATION'] + st['NO_WITNESS']
    print('RESULT', 'PASS' if bad == 0 else 'FAIL', f'{ci}_{ri}', flush=True)


if __name__ == '__main__':
    main()
