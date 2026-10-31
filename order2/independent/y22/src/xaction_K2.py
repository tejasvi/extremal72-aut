"""K action on the first nX + r variables of the I28b order, where the r variables after X are the new syndrome
dims of the first block word(s) (span K-invariant because K fixes those words)."""
import sys, pickle
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from symmetry import write_action
from autgroup import apply_perm
P = Problem(read_code36(22), 36, 16)
FS = P.FS
pk = pickle.load(open("<HOME>/c72_indep/y22/out/sep_I28b_prep.pkl", "rb"))
A = pickle.load(open("<HOME>/c72_indep/y22/out/aut.pkl", "rb")); grp = A["grp"]
K = [grp[g] for g in pickle.load(open("<HOME>/c72_indep/y22/out/kernel_K.pkl", "rb"))]
nwords = int(sys.argv[1])
nX = pk["nX"]; vf = pk["var_funcs"]
first = pk["order"][:nwords]
for y in first:
    assert all(apply_perm(y, k, 36) == y for k in K), "first block word not fixed by K"
pairs = list(pk["sel"])
r = 0
while nX + r < len(vf):
    f = vf[nX + r]
    js = [(y, x) for y in first for x in P.shortened_basis(y) if FS.functional(y, x) == f]
    if not js: break
    pairs.append(js[0]); r += 1
print("first %d block word(s): r = %d W variables" % (nwords, r))
write_action(P, pairs, K, "<HOME>/c72_indep/y22/out/xactionK_b%d.bin" % nwords)
print("written; NX=%d NW=%d" % (nX, r))
