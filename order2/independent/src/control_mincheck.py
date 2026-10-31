"""Build C_B for every control solution (expanded set) and brute-force its weight distribution."""
import sys, json, pickle, subprocess, os
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
D = "<HOME>/c72_indep/"
env = dict(os.environ, TMPDIR=D + "tmp")
d = json.load(open(D + "out/control.json"))
P = Problem(d["Y48"], 24, 12)
cp = pickle.load(open(D + "out/control_prep.pkl", "rb"))
EDf = EngineData(P, cp["order"])
keys = sorted(pickle.load(open(D + "out/control_keys.pkl", "rb"))["exp_keys"])
path = D + "tmp/control_all_codes.txt"
with open(path, "w") as f:
    for v in keys:
        M = EDf.form_from_vars(v)
        rows = P.code_CB(M)
        f.write("48 24\n")
        for r in rows:
            f.write("%016x %016x\n" % (r >> 64, r & ((1 << 64) - 1)))
out = subprocess.run(["nice", "-n", "10", D + "src/mincheck", path], capture_output=True, text=True, env=env).stdout
lines = out.strip().split("\n")
mins = [l for l in lines if l.startswith("MINWEIGHT")]
wds = [l for l in lines if l.startswith("WD")]
from collections import Counter
print("codes checked:", lines[-1], " min weights:", Counter(mins))
print("weight distributions:", Counter(wds))
