"""Find a small K-invariant extension W of the Y22 separator on which K acts (mostly) freely."""
import sys, pickle
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
X = pk["var_funcs"][:pk["nX"]]
nd = len(P.diag)
A28 = [v for v in P.words if v and v & ~O28 == 0 and wt(v) <= 16]
best = []
for b0 in [v for v in P.words if wt(v) == 8]:
    orb = sorted({apply_perm(b0, k, 36) for k in K})
    if len(orb) != 8: continue
    U = 0
    for b in orb: U |= b
    cands = [a for a in A28 if a & U == 0]
    if not cands: continue
    for a in cands[:6]:
        E = Elim()
        for f, c in P.diag: E.add(f, 0)
        for f in X: E.add(f, 0)
        base = len(E)
        W = []
        for b in orb:
            if E.add(FS.functional(a, b), 0)[0]: W.append((a, b))
        best.append((len(W), wt(b0), b0, a, W))
best.sort(key=lambda t: (abs(t[0] - 3), t[1]))
for t in best[:8]:
    print("dimW", t[0], "b0 wt", t[1], "b0 %x a %x" % (t[2], t[3]))
pickle.dump(best[:20], open("<HOME>/c72_indep/y22/out/W_candidates.pkl", "wb"))
print("candidates", len(best))
