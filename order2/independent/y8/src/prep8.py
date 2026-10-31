"""Y8 engine data: X = Z (H' x R'), beta (H' x v'), alpha (u0 x R') first; then U'-part order by mode; then V' w8;
then all remaining words by weight."""
import sys, pickle, time
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from problem import *
from engine_prep import *
from y8_struct import *
from linalg import Elim
t0 = time.time()
P = Problem(read_code36(8), 36, 16)
S = structure(P.words)
FS = P.FS
Zc = [FS.functional(h, r) for h in S["Hb"] for r in S["Rb"]]
Bc = [FS.functional(h, S["vprime"]) for h in S["Hb"]]
Ac = [FS.functional(S["u0"], r) for r in S["Rb"]]
Xc = Zc + Bc + Ac
funcs = {y: [FS.functional(y, x) for x in P.shortened_basis(y)] for y in P.low}
def newdims(E, y):
    tmp = Elim(); tmp.rows = dict(E.rows)
    return sum(tmp.add(f, 0)[0] for f in funcs[y])
def greedy(E, words, key):
    order, remaining = [], list(words)
    while remaining:
        best = min(remaining, key=lambda y: key(E, y))
        for f in funcs[best]: E.add(f, 0)
        order.append(best); remaining.remove(best)
    return order
E = Elim()
for f, c in P.diag: E.add(f, 0)
nX = 0
for f in Xc: nX += E.add(f, 0)[0]
print("independent X functionals:", nX)
U8 = [y for y in P.low if y & ~(m18 | m2) == 0 and wt(y) == 8]
V8 = [y for y in P.low if y & ~(m16 | m2) == 0 and wt(y) == 8]
mode = sys.argv[1]
k_basic = lambda E, y: (newdims(E, y), wt(y), y)
first = []
if mode.startswith("first:"):
    # explicit first U-words given as hex list
    first = [int(t, 16) for t in mode.split(":")[1].split(",")]
    for y in first:
        for f in funcs[y]: E.add(f, 0)
if mode.startswith("kv:") or mode.startswith("vk:"):
    k = int(mode.split(":")[1], 16)
    if mode.startswith("kv:"):
        for f in funcs[k]: E.add(f, 0)
        o = [k] + greedy(E, V8, k_basic)
        o += greedy(E, [y for y in U8 if y != k], k_basic)
    else:
        o = greedy(E, V8, k_basic)
        for f in funcs[k]: E.add(f, 0)
        o += [k] + greedy(E, [y for y in U8 if y != k], k_basic)
elif mode == "vfirst":
    o = greedy(E, V8, k_basic)
    o += greedy(E, U8, k_basic)
else:
    o = first + greedy(E, [y for y in U8 if y not in set(first)], k_basic)
    o += greedy(E, V8, k_basic)
seen = set(o)
rest = sorted([y for y in P.low if y not in seen], key=lambda y: (wt(y), y))
order = o + rest
ED = EngineData(P, order, extra_var_funcs=Xc)
tag = sys.argv[2]
out = "<HOME>/c72_indep/y8/out/y8_%s.eng" % tag
ED.write(out)
fd = {}
for y, d in zip(ED.words, ED.full_depth): fd.setdefault(d, []).append(wt(y))
print(tag, "nv", ED.nv, "events", len(ED.events), "time %.1f" % (time.time() - t0))
print("full depth -> #w8:", [(d, sum(1 for w in fd[d] if w == 8)) for d in sorted(fd) if d <= 80 and any(w == 8 for w in fd[d])])
pickle.dump({"order": order, "var_funcs": ED.var_funcs, "words": ED.words, "full_depth": ED.full_depth, "nX": nX,
             "Hb": S["Hb"], "Rb": S["Rb"], "u0": S["u0"], "vprime": S["vprime"]},
            open(out.replace(".eng", "_prep.pkl"), "wb"))
