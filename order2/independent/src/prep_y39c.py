"""X = Z, beta, alpha; then U-part: greedy (min new dims) over U w8 words; then V w8 words; then the rest."""
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
def greedy_after(P, E, words, funcs):
    order, remaining = [], list(words)
    while remaining:
        best = None
        for y in remaining:
            tmp = Elim(); tmp.rows = dict(E.rows)
            r = sum(tmp.add(f, 0)[0] for f in funcs[y])
            key = (r, wt(y))
            if best is None or key < best[0]: best = (key, y)
        y = best[1]
        for f in funcs[y]: E.add(f, 0)
        order.append(y); remaining.remove(y)
    return order
funcs = {y: [FS.functional(y, x) for x in P.shortened_basis(y)] for y in P.low}
E = Elim()
for f, c in P.diag: E.add(f, 0)
for f in Xc: E.add(f, 0)
U8 = [y for y in P.low if y & ~(m18 | m2) == 0 and wt(y) == 8]
V8 = [y for y in P.low if y & ~(m16 | m2) == 0 and wt(y) == 8]
mode = sys.argv[1] if len(sys.argv) > 1 else "UV"
if mode == "UV":
    o1 = greedy_after(P, E, U8, funcs); o2 = greedy_after(P, E, V8, funcs)
else:
    o1 = greedy_after(P, E, V8, funcs); o2 = greedy_after(P, E, U8, funcs)
first = o1 + o2
seen = set(first)
rest = sorted([y for y in P.low if y not in seen], key=lambda y: (wt(y), y))
order = first + rest
ED = EngineData(P, order, extra_var_funcs=Xc)
out = "<HOME>/c72_indep/out/y39_%s.eng" % mode
ED.write(out)
fd = {}
for y, d in zip(ED.words, ED.full_depth): fd.setdefault(d, []).append(wt(y))
print(mode, "nv", ED.nv, "events", len(ED.events), "time %.1f" % (time.time() - t0))
print("full depth -> #w8 completed:", [(d, sum(1 for w in fd[d] if w == 8)) for d in sorted(fd) if any(w == 8 for w in fd[d])])
pickle.dump({"order": order, "var_funcs": ED.var_funcs, "words": ED.words, "full_depth": ED.full_depth},
            open(out.replace(".eng", "_prep.pkl"), "wb"))
