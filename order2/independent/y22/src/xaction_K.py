import sys, pickle
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from symmetry import write_action
P = Problem(read_code36(22), 36, 16)
pk = pickle.load(open("<HOME>/c72_indep/y22/out/sep_I28W_prep.pkl", "rb"))
A = pickle.load(open("<HOME>/c72_indep/y22/out/aut.pkl", "rb")); grp = A["grp"]
K = [grp[g] for g in pickle.load(open("<HOME>/c72_indep/y22/out/kernel_K.pkl", "rb"))]
assert [P.FS.functional(a, c) for a, c in pk["sel"]] == pk["var_funcs"][:pk["nX"]]
write_action(P, pk["sel"], K, "<HOME>/c72_indep/y22/out/xactionK37.bin")
print("K action on", pk["nX"], "vars written")
