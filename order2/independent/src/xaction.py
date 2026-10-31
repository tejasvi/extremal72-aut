"""Affine action of Aut(Y39) on the 40 X-variables (values of functionals B(h,r), B(h,v'), B(u0,r)).
For g in G (coordinate permutation, (g v)_{p[i]} = v_i) and a form B, B^g(x,y) = B(gx, gy); B^g is a valid form
and C_{B^g} = (g^-1 x g^-1) C_B. Variable phi_i = 'B(y_i, x_i)' takes on B^g the value of 'B(g y_i, g x_i)' on B,
which is a combination of X-variables plus a constant (diagonal functionals)."""
import sys, pickle, struct
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from y39_struct import *
from autgroup import apply_perm
prep = sys.argv[1]       # engine prep pickle (for var_funcs)
out = sys.argv[2]
P = Problem(read_code36(39), 36, 16)
S = structure(P.words)
FS = P.FS
pairs = [(h, r) for h in S["Hb"] for r in S["Rb"]] + [(h, S["vprime"]) for h in S["Hb"]] + [(S["u0"], r) for r in S["Rb"]]
pk = pickle.load(open(prep, "rb"))
var_funcs = pk["var_funcs"]
# identify which pairs were selected as the first 40 variables
sel = []
for i in range(40):
    f = var_funcs[i]
    js = [j for j, (y, x) in enumerate(pairs) if FS.functional(y, x) == f]
    assert js, i
    sel.append(pairs[js[0]])
# elimination over [diag | X vars] with tags
from linalg import Elim
nd = len(P.diag)
E = Elim()
for t, (f, c) in enumerate(P.diag):
    E.add(f, 1 << t)
for i, (y, x) in enumerate(sel):
    ok, _ = E.add(FS.functional(y, x), 1 << (nd + i))
    assert ok
diag_const = sum(1 << t for t, (f, c) in enumerate(P.diag) if c)
grp = pickle.load(open("<HOME>/c72_indep/out/aut39.pkl", "rb"))
assert len(grp) == 34560
Ymask_ok = set(P.words)
def action(p):
    rows, const = [], 0
    for i, (y, x) in enumerate(sel):
        gy, gx = apply_perm(y, p, 36), apply_perm(x, p, 36)
        assert gy in Ymask_ok and gx in Ymask_ok
        combo, resid = E.express(FS.functional(gy, gx))
        assert resid == 0, "image functional not in X-span"
        rows.append(combo >> nd)
        if bin(combo & diag_const & ((1 << nd) - 1)).count("1") & 1:
            const |= 1 << i
    return rows, const
with open(out, "wb") as f:
    f.write(struct.pack("<ii", len(grp), 40))
    nz = 0
    for k, p in enumerate(grp):
        rows, const = action(p)
        # Z-part must depend only on Z
        for i in range(30):
            assert rows[i] >> 30 == 0, "Z image depends on non-Z"
        for r in rows:
            f.write(struct.pack("<Q", r))
        f.write(struct.pack("<Q", const))
        if k % 5000 == 0:
            print(k, flush=True)
print("identity check:", action(tuple(range(36))) == ([1 << i for i in range(40)], 0))
print("written", out)
