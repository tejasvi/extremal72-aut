"""Control test of the two-pass logic: a feasibility filter computed with a different variable order after the
separator must keep every representative that has solutions."""
import sys, json, pickle, subprocess, os, random
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
D = "<HOME>/c72_indep/"
env = dict(os.environ, TMPDIR=D + "tmp")
d = json.load(open(D + "out/control.json"))
P = Problem(d["Y48"], 24, 12)
cp = pickle.load(open(D + "out/control_prep.pkl", "rb"))
sp = pickle.load(open(D + "out/control_sym_prep.pkl", "rb"))
nX = sp["ZB"] + sp["WB"]
Xf = sp["var_funcs"][:nX]
order = list(cp["order"])
random.seed(5)
random.shuffle(order)
ED2 = EngineData(P, order, extra_var_funcs=Xf)
assert ED2.var_funcs[:nX] == Xf
ED2.write(D + "out/control_sym_alt.eng")
mask = (1 << nX) - 1
withsol = set()
for f in ("res_chunk_0.txt", "res_chunk_1.txt"):
    for l in open(D + "out/csym/" + f):
        if l.startswith("SOL"):
            withsol.add(int(l.split()[2], 16) & mask)
reps = [int(l.split()[1], 16) for l in open(D + "out/control_sym_reps.txt")]
res = {}
for dmax in (20, 30, 44):
    out = subprocess.run(["nice", "-n", "10", D + "src/engine5", D + "out/control_sym_alt.eng", "feas",
                          D + "out/control_sym_prefixes.txt", str(nX), str(dmax), "-"], capture_output=True, text=True, env=env).stdout
    feas = {int(l.split()[2], 16) for l in out.split("\n") if l.startswith("FEAS") and l.split()[3] == "1"}
    print("filter depth", dmax, ": reps kept", len(feas), "of", len(reps), "; reps with solutions", len(withsol),
          "; all kept:", withsol <= feas, "; kept at full depth == reps with solutions:" if dmax == 44 else "",
          (feas == withsol) if dmax == 44 else "")
