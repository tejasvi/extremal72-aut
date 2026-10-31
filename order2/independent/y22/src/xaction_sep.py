"""Affine action of the separator-preserving group on the separator variables (pairs 'sel' from a prep pickle).
usage: xaction_sep.py K DIR PREP_PKL GROUP_IDX_PKL|all OUT_BIN OUT_GENS"""
import sys, pickle
K = int(sys.argv[1]); DIR = sys.argv[2]
sys.path.insert(0, DIR + "/src")
from problem import *
from symmetry import write_action
P = Problem(read_code36(K), 36, 16)
pk = pickle.load(open(sys.argv[3], "rb"))
sel = pk["sel"]
assert [P.FS.functional(a, c) for a, c in sel] == pk["var_funcs"][:len(sel)]
A = pickle.load(open(DIR + "/out/aut.pkl", "rb"))
grp, gens = A["grp"], A["gens"]
if sys.argv[4] != "all":
    idx = pickle.load(open(sys.argv[4], "rb"))
    perms = [grp[i] for i in idx]
else:
    perms = grp
write_action(P, sel, perms, sys.argv[5])   # asserts invariance of span(X) + Diag for every element
pi = {p: i for i, p in enumerate(perms)}
if sys.argv[4] == "all":
    gi = [pi[tuple(g)] for g in gens]
else:
    gi = list(range(len(perms)))   # subgroup: use all elements as generators
open(sys.argv[6], "w").write(" ".join(map(str, gi)) + "\n")
print("action maps:", len(perms), "elements; generators", gi[:10], "...", "identity index", pi[tuple(range(36))])
