import sys, pickle, time
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from orders import greedy_word_order
from y39_struct import *
t0 = time.time()
P = Problem(read_code36(39), 36, 16)
S = structure(P.words)
FS = P.FS
Xc = [FS.functional(u, r) for u in S["Ub"] for r in S["Rb"]] + [FS.functional(h, S["vprime"]) for h in S["Hb"]]
lowset = set(P.low)
Uw = [y for y in P.low if y & ~(m18 | m2) == 0]
Vw = [y for y in P.low if y & ~(m16 | m2) == 0]
# greedy within U then V (after X); greedy_word_order starts from diag only, so seed by passing X as pseudo-words:
from linalg import Elim
def greedy_after(P, base_funcs, words):
    FS = P.FS
    funcs = {y: [FS.functional(y, x) for x in P.shortened_basis(y)] for y in words}
    E = Elim()
    for f, c in P.diag: E.add(f, 0)
    for f in base_funcs: E.add(f, 0)
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
        base_funcs = base_funcs + funcs[y]
    return order, base_funcs
ordU, bf = greedy_after(P, Xc, Uw)
ordV, bf = greedy_after(P, bf, Vw)
UV = set(Uw) | set(Vw)
rest = sorted([y for y in P.low if y not in UV], key=lambda y: (wt(y), y))
order = ordU + ordV + rest
ED = EngineData(P, order, Rmax=3, extra_var_funcs=Xc)
print("nv", ED.nv, "events", len(ED.events), "time", time.time() - t0)
# count X vars: independent among Xc
E = Elim()
for f, c in P.diag: E.add(f, 0)
nX = sum(E.add(f, 0)[0] for f in Xc)
print("independent X functionals:", nX)
ED.write("<HOME>/c72_indep/out/y39_X.eng")
pickle.dump({"order": order, "nX": nX, "var_funcs": ED.var_funcs, "full_depth": ED.full_depth,
             "words": ED.words}, open("<HOME>/c72_indep/out/y39_X_prep.pkl", "wb"))
from collections import Counter
fd = Counter(ED.full_depth)
print("full-check depth histogram (depth: #words):", sorted(fd.items()))
