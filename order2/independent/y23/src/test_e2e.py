"""End-to-end test of the formulation on random forms: predicted low-weight counts of C_B (from syndromes / cosets)
vs brute-force weight distribution (mincheck). usage: test_e2e.py {y39|y48} SEED"""
import sys, json, random, subprocess, os
sys.path.insert(0, "<HOME>/c72_indep/y23/src")
from problem import *
from linalg import solve
from write_code import write_rows
from itertools import combinations
D = "<HOME>/c72_indep/y23/"
which, seed = sys.argv[1], int(sys.argv[2])
if which == "y23":
    P = Problem(read_code36(23), 36, 16)
elif which == "y8":
    P = Problem(read_code36(8), 36, 16)
elif which == "y39":
    P = Problem(read_code36(39), 36, 16)
else:
    P = Problem(json.load(open("<HOME>/c72_indep/out/control.json"))["Y48"], 24, 12)
random.seed(seed)
v = random.getrandbits(P.FS.N)
funcs = [f for f, c in P.diag]
tg = [c ^ (bin(f & v).count("1") & 1) for f, c in P.diag]
M = P.vec_to_gram(v ^ solve(funcs, tg))
assert P.is_valid_form(M)
n, dd = P.n, P.dd
# predicted counts of codewords of weight w < dd: 2 * sum_y #{e outside y: syndrome(e) = s_y, |y| + 2|e| = w}
pred = {}
for y in P.words:
    if y == 0 or wt(y) >= dd:
        continue
    xb = P.shortened_basis(y)
    s = sum(P.B(M, y, x) << j for j, x in enumerate(xb))
    T = [i for i in range(n) if not y >> i & 1]
    maxe = (dd - wt(y) - 1) // 2
    for k in range(0, maxe + 1):
        for c in combinations(T, k):
            e = 0
            for i in c: e |= 1 << i
            if sum((wt(e & x) & 1) << j for j, x in enumerate(xb)) == s:
                w = wt(y) + 2 * k
                pred[w] = pred.get(w, 0) + 2
rows = P.code_CB(M)
path = D + "tmp/e2e_%s_%d.txt" % (which, seed)
write_rows(rows, 2 * n, path)
out = subprocess.run(["nice", "-n", "10", D + "src/mincheck", path], capture_output=True, text=True,
                     env=dict(os.environ, TMPDIR=D + "tmp")).stdout
wdline = [l for l in out.split("\n") if l.startswith("WD")][0]
wd = {int(a): int(b) for a, b in (t.split(":") for t in wdline.split()[1:])}
brute = {w: c for w, c in wd.items() if 0 < w < dd}
print(which, "seed", seed, "predicted", dict(sorted(pred.items())), "brute", dict(sorted(brute.items())),
      "MATCH" if pred == brute else "MISMATCH")
print(out.strip().split("\n")[1])
