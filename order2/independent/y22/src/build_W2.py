"""Greedy choice of up to m functionals B(a, b) (b with K-orbit of size 8, a in Y(O28) disjoint from the orbit)
maximizing the fraction of sample X-reps on which K acts freely on W (translation homomorphism injective)."""
import sys, pickle, random
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from autgroup import apply_perm
from linalg import Elim
P = Problem(read_code36(22), 36, 16)
FS = P.FS
A = pickle.load(open("<HOME>/c72_indep/y22/out/aut.pkl", "rb")); grp = A["grp"]
K = [grp[g] for g in pickle.load(open("<HOME>/c72_indep/y22/out/kernel_K.pkl", "rb"))]
O28 = 0x57ffdfbf2
pk = pickle.load(open("<HOME>/c72_indep/y22/out/sep_I28b_prep.pkl", "rb"))
sel = pk["sel"]; nX = len(sel)
nd = len(P.diag)
E0 = Elim()
for t, (f, c) in enumerate(P.diag): E0.add(f, 1 << t)
for i, (a, c) in enumerate(sel): E0.add(FS.functional(a, c), 1 << (nd + i))
dconst = sum(1 << t for t, (f, c) in enumerate(P.diag) if c)
A28 = [v for v in P.words if v and v & ~O28 == 0 and wt(v) <= 16]
reps = [int(l.split()[1], 16) for l in open("<HOME>/c72_indep/y22/out/xreps22.txt")]
random.seed(5)
samp = random.sample(reps, 1500)
# For a pair (a, b): translation by k is B(a, k b) - B(a, b) = B(a, kb + b) which must lie in X-span: value = lin(X)+const
cand = []
for b in [v for v in P.words if 8 <= wt(v) <= 10]:
    orb = [apply_perm(b, k, 36) for k in K]
    if len(set(orb)) != 8: continue
    U = 0
    for o in orb: U |= o
    for a in [a for a in A28 if a & U == 0][:4]:
        tr = []
        ok = True
        for o in orb:
            combo, resid = E0.express(FS.functional(a, o ^ b)) if (o ^ b) else (0, 0)
            if resid: ok = False; break
            tr.append(((combo >> nd), bin(combo & dconst & ((1 << nd) - 1)).count("1") & 1))
        if ok:
            cand.append((a, b, tr))
print("candidate pairs", len(cand))
# evaluate translation bits per sample rep: bit for k = parity(mask & x) ^ const
def tbits(c, x):
    return [ (bin(m & x).count("1") & 1) ^ cc for (m, cc) in c[2] ]
chosen = []
E = Elim(); E.rows = dict(E0.rows)
cur_vecs = [[0] * 8 for _ in samp]
m = int(sys.argv[1])
for step in range(m):
    best = None
    for c in cand:
        f = FS.functional(c[0], c[1])
        tmp = Elim(); tmp.rows = dict(E.rows)
        if not tmp.add(f, 0)[0]: continue
        nfree = 0
        for si, x in enumerate(samp):
            tb = tbits(c, x)
            vecs = {(cur_vecs[si][k] << 1) | tb[k] for k in range(8)}
            if len(vecs) == 8: nfree += 1
        if best is None or nfree > best[0]: best = (nfree, c)
    nfree, c = best
    chosen.append(c)
    E.add(FS.functional(c[0], c[1]), 0)
    for si, x in enumerate(samp):
        tb = tbits(c, x)
        cur_vecs[si] = [(cur_vecs[si][k] << 1) | tb[k] for k in range(8)]
    print("step", step + 1, "pair a=%x b=%x" % (c[0], c[1]), "free fraction %.3f" % (nfree / len(samp)))
pickle.dump({"Wp": [(c[0], c[1]) for c in chosen]}, open("<HOME>/c72_indep/y22/out/W2_m%d.pkl" % m, "wb"))
