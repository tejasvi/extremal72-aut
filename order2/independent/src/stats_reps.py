"""For V-feasible reps: how often is a_u = 0 for each U-word (a_u = B(u, .)|_R, determined by X)."""
import sys, pickle
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from y39_struct import *
from linalg import Elim
from collections import Counter
P = Problem(read_code36(39), 36, 16)
S = structure(P.words)
FS = P.FS
pk = pickle.load(open("<HOME>/c72_indep/out/y39_UV_prep.pkl", "rb"))
vf = pk["var_funcs"]
nd = len(P.diag)
E = Elim()
for t, (f, c) in enumerate(P.diag): E.add(f, 1 << t)
for i in range(40): E.add(vf[i], 1 << (nd + i))
dconst = sum(1 << t for t, (f, c) in enumerate(P.diag) if c)
U8 = [y for y in P.low if y & ~(m18 | m2) == 0 and wt(y) == 8]
# a_u components: B(u, r) for r in Rb -> express in X vars
aexpr = {}
for u in U8:
    rows = []
    for r in S["Rb"]:
        combo, resid = E.express(FS.functional(u, r))
        assert resid == 0
        rows.append((combo >> nd, bin(combo & dconst & ((1 << nd) - 1)).count("1") & 1))
    aexpr[u] = rows
reps = [int(l.split()[1], 16) for l in open("<HOME>/c72_indep/out/pass1/vfeasible.txt")]
import random
random.seed(1)
samp = random.sample(reps, 5000)
cnt = Counter()
nzero = Counter()
for x in samp:
    k = 0
    for u in U8:
        a = sum(((bin(r & x).count("1") + c) & 1) << j for j, (r, c) in enumerate(aexpr[u]))
        if a == 0:
            cnt[u] += 1; k += 1
    nzero[k] += 1
print("distribution of #U8 words with a_u = 0 per rep:", sorted(nzero.items()))
print("most frequent a_u=0 words (fraction):", [(hex(u), round(c / len(samp), 3), wt(u & m2)) for u, c in cnt.most_common(12)])
