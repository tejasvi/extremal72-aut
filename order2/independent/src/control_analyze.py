"""Control analysis: canonical keys of solutions from the full run and the symmetry-reduced run; expansion under H;
QR48 membership; brute-force minimum weight of every solution code."""
import sys, json, pickle, subprocess, os
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from symmetry import form_image
from write_code import write_rows
D = "<HOME>/c72_indep/"
env = dict(os.environ, TMPDIR=D + "tmp")
d = json.load(open(D + "out/control.json"))
P = Problem(d["Y48"], 24, 12)
cp = pickle.load(open(D + "out/control_prep.pkl", "rb"))
EDf = EngineData(P, cp["order"])                       # basis of the full run (out/control.eng)
assert EDf.vars_from_form(cp["M_qr"]) == cp["v_qr"] == 0x50533672a7e
sp = pickle.load(open(D + "out/control_sym_prep.pkl", "rb"))
from orders import greedy_word_order
Xf = sp["var_funcs"][:sp["ZB"] + sp["WB"]]
EDs = EngineData(P, cp["order"], extra_var_funcs=Xf)  # same construction as control_sym_prep (order = greedy)
assert EDs.var_funcs == sp["var_funcs"], "sym basis mismatch"
def sols(paths):
    out = []
    for p in paths:
        for l in open(p):
            if l.startswith("SOL"):
                a, b = l.split()[1:3]
                out.append((int(a, 16) << 64) | int(b, 16))
    return out
full_files = sys.argv[1:] if sys.argv[1:] else [D + "out/control_full.txt"]
full = sols(full_files)
sym = sols([D + "out/csym/res_chunk_0.txt", D + "out/csym/res_chunk_1.txt"])
print("full-run solutions:", len(full), "distinct:", len(set(full)), " sym-run solutions:", len(sym))
key = EDf.vars_from_form
full_keys = set()
for v in full:
    M = EDf.form_from_vars(v)
    assert not EDf.check_form(M), "full-run solution fails direct check"
    full_keys.add(key(M))
sym_keys, sym_forms = set(), []
for v in sym:
    M = EDs.form_from_vars(v)
    assert not EDs.check_form(M), "sym-run solution fails direct check"
    sym_forms.append(M)
exp = set()
for M in sym_forms:
    for h in sp["Hgrp"]:
        exp.add(key(form_image(P, M, h)))
print("sym solutions expanded under H:", len(exp))
print("expanded == full:", exp == full_keys, " expanded - full:", len(exp - full_keys), " full - expanded:", len(full_keys - exp))
print("QR48 form in full set:", cp["v_qr"] in full_keys, " in expanded set:", cp["v_qr"] in exp)
pickle.dump({"full_keys": full_keys, "exp_keys": exp}, open(D + "out/control_keys.pkl", "wb"))
