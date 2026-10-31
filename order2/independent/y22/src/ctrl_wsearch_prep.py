"""Control test of the two-stage (G on Z, kernel K on Z+w) reduction: action files for the QR48 control separator."""
import sys, pickle, struct
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from symmetry import write_action
import json
D = "<HOME>/c72_indep/"
d = json.load(open(D + "out/control.json"))
P = Problem(d["Y48"], 24, 12)
sp = pickle.load(open(D + "out/control_sym_prep.pkl", "rb"))
ZB, WB = sp["ZB"], sp["WB"]
y0, y1 = sp["y0"], sp["y1"]
# reconstruct the separator pairs in variable order
FS = P.FS
cand = [(y0, x) for x in P.shortened_basis(y0)] + [(y1, x) for x in P.shortened_basis(y1)]
pairs = []
for i in range(ZB + WB):
    f = sp["var_funcs"][i]
    pairs.append(next(p for p in cand if FS.functional(*p) == f))
H = sp["Hgrp"]
O = D + "y22/out/ctrlK/"
write_action(P, pairs[:ZB], H, O + "actZ.bin")
data = open(O + "actZ.bin", "rb").read()
ng, nx = struct.unpack("<ii", data[:8])
ident = data[8:8 + (nx + 1) * 8]
Kc = [H[g] for g in range(ng) if data[8 + g * (nx + 1) * 8: 8 + (g + 1) * (nx + 1) * 8] == ident]
print("|H| =", len(H), "kernel on Z |Kc| =", len(Kc))
write_action(P, pairs, Kc, O + "actK.bin")
print("ZB", ZB, "WB", WB)
