"""X = Z, beta, alpha first; then U-part with selectable strategy; then V8; then rest."""
import sys, pickle, time
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from y39_struct import *
from linalg import Elim
t0 = time.time()
P = Problem(read_code36(39), 36, 16)
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
def completes(E, y, pool):
    tmp = Elim(); tmp.rows = dict(E.rows)
    for f in funcs[y]: tmp.add(f, 0)
    return sum(1 for z in pool if all(tmp.reduce(f)[0] == 0 for f in funcs[z]))
def greedy(E, words, key):
    order, remaining = [], list(words)
    while remaining:
        best = min(remaining, key=lambda y: key(E, y, remaining))
        for f in funcs[best]: E.add(f, 0)
        order.append(best); remaining.remove(best)
    return order
E = Elim()
for f, c in P.diag: E.add(f, 0)
for f in Xc: E.add(f, 0)
H8 = [y for y in P.low if y & ~m18 == 0 and wt(y) == 8]
U8 = [y for y in P.low if y & ~(m18 | m2) == 0 and wt(y) == 8]
U602 = [y for y in U8 if y not in set(H8)]
V8 = [y for y in P.low if y & ~(m16 | m2) == 0 and wt(y) == 8]
mode = sys.argv[1]
k_basic = lambda E, y, rem: (newdims(E, y), wt(y), y)
if mode == "base":
    o = greedy(E, U8, k_basic)
elif mode == "602first":
    o = greedy(E, U602, k_basic) + greedy(E, H8, k_basic)
elif mode == "H8first":
    o = greedy(E, H8, k_basic) + greedy(E, U602, k_basic)
elif mode == "tie602":
    o = greedy(E, U8, lambda E, y, rem: (newdims(E, y), 0 if y in set(U602) else 1, y))
elif mode == "hstar":
    hs = S["Hb"][5]
    assert hs in U8
    for f in funcs[hs]: E.add(f, 0)
    o = [hs] + greedy(E, [y for y in U8 if y != hs], k_basic)
elif mode == "lookahead":
    o = greedy(E, U8, lambda E, y, rem: (newdims(E, y) - 0.6 * completes(E, y, rem), y))
o += greedy(E, V8, k_basic)
seen = set(o)
rest = sorted([y for y in P.low if y not in seen], key=lambda y: (wt(y), y))
order = o + rest
ED = EngineData(P, order, extra_var_funcs=Xc)
out = "<HOME>/c72_indep/out/y39_U_%s.eng" % mode
ED.write(out)
fd = {}
for y, d in zip(ED.words, ED.full_depth): fd.setdefault(d, []).append(wt(y))
print(mode, "nv", ED.nv, "events", len(ED.events), "time %.1f" % (time.time() - t0))
print("full depth -> #w8:", [(d, sum(1 for w in fd[d] if w == 8)) for d in sorted(fd) if d <= 80 and any(w == 8 for w in fd[d])])
pickle.dump({"order": order, "var_funcs": ED.var_funcs, "words": ED.words, "full_depth": ED.full_depth},
            open(out.replace(".eng", "_prep.pkl"), "wb"))
