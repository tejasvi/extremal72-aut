"""Diagnose file constraints not matched by indep_check: compare with every low word of the same weight."""
import sys, pickle, itertools, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE + '/../../../model')
sys.path.insert(0, HERE + '/../scripts')
from autinv import load
from indep_check import GF2, parse_instance, apply_perm, joint_equiv
M = 36; K = 18
ci, ri = int(sys.argv[1]), int(sys.argv[2])
inst = f'{HERE}/../../../impl1_runs/lwinst/lwf_{ci}_{ri}.txt'
P = pickle.load(open(inst + '.pkl', 'rb')); w, free, entf, N = P['w'], P['free'], P['entf'], P['N']
MP = pickle.load(open(f'{HERE}/../chk/map_{ci}_{ri}.pkl', 'rb')); beta = MP['beta']; cmap = MP['cmap']
Nf, NLEV, vs, cons = parse_instance(inst)
un = [i for i in range(len(cons)) if i not in cmap]
print('unmatched', un)
codes = load(); Yall = [0]
for g in codes[ci]: Yall = Yall + [s ^ g for s in Yall]
E = [(i, j) for i in range(K) for j in range(i, K)]; eidx = {e: n for n, e in enumerate(E)}
aff = [vm | (c << N) for (vm, c) in entf]
Gaff = [[aff[eidx[(min(a, b), max(a, b))]] for b in range(K)] for a in range(K)]
WB = GF2()
for k, x in enumerate(w): WB.add(x, 1 << k)
def coords(x):
    v, t = WB.reduce(x, 0); assert v == 0; return t
def mine(y):
    wy = y.bit_count(); r = (16 - wy) // 2; cy = coords(y)
    yrow = []
    for b in range(K):
        f = 0
        for a in range(K):
            if (cy >> a) & 1: f ^= Gaff[a][b]
        yrow.append(f)
    KB = GF2(); us = []
    for k in range(K):
        ok, tag = KB.add(w[k] & y, 1 << k)
        if not ok:
            u = 0
            for j in range(K):
                if (tag >> j) & 1: u ^= w[j]
            us.append((u, tag))
    Mf = []
    for (u, tag) in us:
        f = 0
        for b in range(K):
            if (tag >> b) & 1: f ^= yrow[b]
        Mf.append((f & ((1 << N) - 1), f >> N))
    cpos = [p for p in range(M) if not (y >> p) & 1]
    colp = {p: sum(((u >> p) & 1) << s for s, (u, t) in enumerate(us)) for p in cpos}
    bad = set()
    for k in range(r):
        for sub in itertools.combinations(cpos, k):
            s = 0
            for p in sub: s ^= colp[p]
            bad.add(s)
    B = GF2()
    for (vm, c) in Mf: B.add(vm | (c << N))
    return Mf, bad, B.canon()
for idx in un:
    lv, wt, forms, bad = cons[idx]
    B = GF2()
    for (vm, c) in forms: B.add(vm | (c << N))
    key = B.canon()
    print(f'constraint {idx}: lv {lv} wt {wt} m {len(forms)} nbad {len(bad)} rank {B.rank()}')
    # same-key constraints in file
    same = []
    for j, (lv2, wt2, f2, b2) in enumerate(cons):
        if wt2 != wt or len(f2) != len(forms): continue
        B2 = GF2()
        for (vm, c) in f2: B2.add(vm | (c << N))
        if B2.canon() == key: same.append(j)
    print('  file constraints with same key and weight:', same, 'their matched words:', [[hex(y) for y in cmap.get(j, [])] for j in same])
    for j in same:
        if j != idx:
            ok, rk, info = joint_equiv(len(forms), forms, set(bad), len(cons[j][2]), cons[j][2], set(cons[j][3]), N)
            print('   predicate equal to constraint', j, ':', ok, rk, info)
    nkey = 0; neq = 0; eqs = []
    for y in Yall:
        if y.bit_count() != wt: continue
        Mf, mb, k2 = mine(y)
        if k2 != key: continue
        nkey += 1
        ok, rk, info = joint_equiv(len(forms), forms, set(bad), len(Mf), Mf, mb, N)
        if ok: neq += 1; eqs.append(hex(y))
    print(f'  words of weight {wt} with same key: {nkey}, predicate-equivalent: {neq}', eqs[:6])
