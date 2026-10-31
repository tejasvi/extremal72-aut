"""Dimension of span(X + {B(a,b) : a in Y(O28) low words, b in S, a & b = 0}) - dim X for candidate sets S."""
import sys, pickle
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from linalg import Elim
P = Problem(read_code36(22), 36, 16)
FS = P.FS
O8 = 0xa8002040d; O28 = 0x57ffdfbf2
pk = pickle.load(open("<HOME>/c72_indep/y22/out/sep_I28b_prep.pkl", "rb"))
X = pk["var_funcs"][:pk["nX"]]
E0 = Elim()
for f, c in P.diag: E0.add(f, 0)
for f in X: E0.add(f, 0)
base = len(E0)
A28 = [v for v in P.words if v and v & ~O28 == 0 and wt(v) <= 12]
for name, S in (("w8 |b&O8|=4", [v for v in P.words if wt(v) == 8 and wt(v & O8) == 4]),
                ("w8 |b&O8|=1", [v for v in P.words if wt(v) == 8 and wt(v & O8) == 1]),
                ("w10 |b&O8|=4", [v for v in P.words if wt(v) == 10 and wt(v & O8) == 4]),
                ("1_O8 + stuff: words b with b&O8 == O8", [v for v in P.words if v & O8 == O8 and wt(v) <= 16])):
    E = Elim(); E.rows = dict(E0.rows)
    n = 0
    for b in S:
        for a in A28:
            if a & b == 0:
                E.add(FS.functional(a, b), 0); n += 1
    print(name, "|S|", len(S), "pairs", n, "extra dims", len(E) - base)
