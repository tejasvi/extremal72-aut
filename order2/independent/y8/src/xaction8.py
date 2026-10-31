"""Affine action of Aut(Y8) on the 40 X-variables, generator indices, and the canonical-kernel table."""
import sys, pickle, struct
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from problem import *
from y8_struct import *
from symmetry import write_action
from autgroup import apply_perm
from linalg import Elim
D = "<HOME>/c72_indep/y8/out/"
prep = sys.argv[1]
P = Problem(read_code36(8), 36, 16)
FS = P.FS
pk = pickle.load(open(prep, "rb"))
var_funcs = pk["var_funcs"]
Hb, Rb, u0, vp = pk["Hb"], pk["Rb"], pk["u0"], pk["vprime"]
pairs = [(h, r) for h in Hb for r in Rb] + [(h, vp) for h in Hb] + [(u0, r) for r in Rb]
sel = []
for i in range(40):
    js = [j for j, (y, x) in enumerate(pairs) if FS.functional(y, x) == var_funcs[i]]
    assert js, i
    sel.append(pairs[js[0]])
A = pickle.load(open(D + "aut8.pkl", "rb"))
grp, gens = A["grp"], A["gens"]
assert len(grp) == 2304
write_action(P, sel, grp, D + "xaction8.bin")
idx = {p: i for i, p in enumerate(grp)}
gi = [idx[tuple(g)] for g in gens]
open(D + "aut8_gens.txt", "w").write(" ".join(map(str, gi)) + "\n")
print("generators", gi, "identity index", idx[tuple(range(36))])
# canonical kernel table: H' weight-8 words, their G-orbits, canonical word = min of orbit, g with g(c) = w
H8 = sorted(v for v in P.words if v and v & ~m18 == 0 and wt(v) == 8)
assert len(H8) == 45
orbit_of, classes = {}, []
for w in H8:
    if w in orbit_of: continue
    orb = sorted({apply_perm(w, p, 36) for p in grp})
    assert all(o in set(H8) for o in orb)
    for o in orb: orbit_of[o] = len(classes)
    classes.append(orb)
canon_word = [orb[0] for orb in classes]
print("H' w8 orbit sizes:", [len(o) for o in classes], "canonical words:", [hex(c) for c in canon_word])
nd = len(P.diag)
E = Elim()
for t, (f, c) in enumerate(P.diag): E.add(f, 1 << t)
for i in range(40): E.add(var_funcs[i], 1 << (nd + i))
dconst = sum(1 << t for t, (f, c) in enumerate(P.diag) if c)
lines = [str(len(H8))]
for w in H8:
    cl = orbit_of[w]
    c = canon_word[cl]
    g = next(i for i, p in enumerate(grp) if apply_perm(c, p, 36) == w)
    lines.append("%d %d %d" % (cl, g, H8.index(c)))
    for r in Rb:
        combo, resid = E.express(FS.functional(w, r))
        assert resid == 0
        lines.append("%x %d" % (combo >> nd, bin(combo & dconst & ((1 << nd) - 1)).count("1") & 1))
open(D + "canon8.txt", "w").write("\n".join(lines) + "\n")
pickle.dump({"H8": H8, "classes": classes, "canon_word": canon_word, "sel": sel}, open(D + "canon8.pkl", "wb"))
print("written")
