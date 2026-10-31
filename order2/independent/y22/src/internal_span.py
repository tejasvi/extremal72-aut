"""Dimension of span{B(a,c) : a, c in Y(S) words of weight <= wmax, a & c = 0} modulo the diagonal functionals."""
import sys
K = int(sys.argv[1]); DIR = sys.argv[2]; S = int(sys.argv[3], 16); wmax = int(sys.argv[4])
sys.path.insert(0, DIR + "/src")
from problem import *
from linalg import Elim
P = Problem(read_code36(K), 36, 16)
FS = P.FS
sub = [v for v in P.words if v and v & ~S == 0]
low = [v for v in sub if wt(v) <= wmax]
print("Y(S): dim", rank(sub, 36), "words of weight <=", wmax, ":", len(low))
E = Elim()
for f, c in P.diag: E.add(f, 0)
base = len(E)
pairs = [(a, c) for i, a in enumerate(low) for c in low[i + 1:] if a & c == 0]
print("disjoint pairs:", len(pairs))
sel = []
for a, c in pairs:
    if E.add(FS.functional(a, c), 0)[0]:
        sel.append((a, c))
print("span dimension (mod diag):", len(E) - base)
import pickle
pickle.dump(sel, open(DIR + "/out/internal_span_%x.pkl" % S, "wb"))
