"""Expand control solutions (SOL lines in the control_sym.eng basis) under H and compare with the 5760 reference."""
import sys, json, pickle
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from engine_prep import *
from symmetry import form_image
D = "<HOME>/c72_indep/"
P = Problem(json.load(open(D + "out/control.json"))["Y48"], 24, 12)
cp = pickle.load(open(D + "out/control_prep.pkl", "rb"))
sp = pickle.load(open(D + "out/control_sym_prep.pkl", "rb"))
EDf = EngineData(P, cp["order"])
EDs = EngineData(P, cp["order"], extra_var_funcs=sp["var_funcs"][:sp["ZB"] + sp["WB"]])
assert EDs.var_funcs == sp["var_funcs"]
ref = pickle.load(open(D + "out/control_keys.pkl", "rb"))["full_keys"]
sols = []
for l in open(sys.argv[1]):
    if l.startswith("SOL"):
        a, b = l.split()[1:3]; sols.append((int(a, 16) << 64) | int(b, 16))
exp = set()
for v in sols:
    M = EDs.form_from_vars(v)
    assert not EDs.check_form(M)
    for h in sp["Hgrp"]:
        exp.add(EDf.vars_from_form(form_image(P, M, h)))
print("solutions found", len(sols), "; expanded under H:", len(exp), "; equal to the 5760 reference set:", exp == ref)
