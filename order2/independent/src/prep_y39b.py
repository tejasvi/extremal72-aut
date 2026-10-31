"""X ordered as Z (H x R), beta (H x v'), alpha (u0 x R); then U-part by chain order; then V-part; then rest."""
import sys, pickle, time
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from y39_struct import *
from linalg import Elim
P = Problem(read_code36(39), 36, 16)
S = structure(P.words)
FS = P.FS
Zc = [FS.functional(h, r) for h in S["Hb"] for r in S["Rb"]]
Bc = [FS.functional(h, S["vprime"]) for h in S["Hb"]]
Ac = [FS.functional(S["u0"], r) for r in S["Rb"]]
Xc = Zc + Bc + Ac
order = [y for y in P.low if y & ~(m18 | m2) == 0 and wt(y) == 8]
ED = EngineData(P, order, Rmax=3, extra_var_funcs=Xc)
ED.write("<HOME>/c72_indep/out/y39_Xb2.eng")
E = Elim()
for f, c in P.diag: E.add(f, 0)
print("indep Z", sum(E.add(f, 0)[0] for f in Zc), "beta", sum(E.add(f, 0)[0] for f in Bc), "alpha", sum(E.add(f, 0)[0] for f in Ac))
