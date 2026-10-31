"""Kernel K of the action of Aut(Y22) on the separator variables; its action on coordinates and words."""
import sys, pickle, struct
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from autgroup import apply_perm
P = Problem(read_code36(22), 36, 16)
A = pickle.load(open("<HOME>/c72_indep/y22/out/aut.pkl", "rb")); grp = A["grp"]
data = open("<HOME>/c72_indep/y22/out/xaction22.bin", "rb").read()
ng, nx = struct.unpack("<ii", data[:8])
ident = data[8:8 + (nx + 1) * 8]
K = []
for g in range(ng):
    off = 8 + g * (nx + 1) * 8
    if data[off:off + (nx + 1) * 8] == ident:
        K.append(g)
print("|K| =", len(K))
O8 = 0xa8002040d; O28 = 0x57ffdfbf2
for g in K:
    p = grp[g]
    moved = [i for i in range(36) if p[i] != i]
    print("g", g, "moved coords", moved, "in O8:", [i for i in moved if O8 >> i & 1])
low = [v for v in P.low]
fixedw = sum(1 for v in low if all(apply_perm(v, grp[g], 36) == v for g in K))
print("low-weight words fixed by all of K:", fixedw, "of", len(low))
pickle.dump(K, open("<HOME>/c72_indep/y22/out/kernel_K.pkl", "wb"))
