"""Control: separator symmetry test. H = Stab(y0) cap Stab(y1) in Aut(Y48) for disjoint weight-6 words y0, y1;
separator Z = syndrome functionals of y0, W = syndrome functionals of y1 (both H-invariant spans)."""
import sys, json, pickle
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from orders import greedy_word_order
from autgroup import low_weight_spanning_set, aut_group, apply_perm
from symmetry import enumerate_group, write_action
from linalg import Elim
D = "<HOME>/c72_indep/out/"
d = json.load(open(D + "control.json"))
Y48 = d["Y48"]
P = Problem(Y48, 24, 12)
S, w = low_weight_spanning_set(Y48, 24)
order_, gens = aut_group(S, 24)
grp = enumerate_group(gens, 24)
assert len(grp) == 138240
W6 = sorted(y for y in P.words if wt(y) == 6)
y0 = W6[0]
y1 = [y for y in W6 if y & y0 == 0][0]
Hgrp = [p for p in grp if apply_perm(y0, p, 24) == y0 and apply_perm(y1, p, 24) == y1]
print("|H| =", len(Hgrp))
FS = P.FS
E = Elim()
for f, c in P.diag: E.add(f, 0)
zp = [(y0, x) for x in P.shortened_basis(y0) if E.add(FS.functional(y0, x), 0)[0]]
wp = [(y1, x) for x in P.shortened_basis(y1) if E.add(FS.functional(y1, x), 0)[0]]
ZB, WB = len(zp), len(wp)
print("ZB", ZB, "WB", WB)
xpairs = zp + wp
Xf = [FS.functional(y, x) for y, x in xpairs]
order = greedy_word_order(P)
ED = EngineData(P, order, extra_var_funcs=Xf)
assert ED.var_funcs[:ZB + WB] == Xf
ED.write(D + "control_sym.eng")
write_action(P, xpairs, Hgrp, D + "control_sym_action.bin")
open(D + "control_sym_gens.txt", "w").write(" ".join(str(i) for i in range(len(Hgrp))) + "\n")
pickle.dump({"ZB": ZB, "WB": WB, "var_funcs": ED.var_funcs, "Hgrp": Hgrp, "y0": y0, "y1": y1},
            open(D + "control_sym_prep.pkl", "wb"))
print("ok")
