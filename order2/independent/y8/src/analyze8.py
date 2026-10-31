import sys, pickle
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from codes import *
from autgroup import low_weight_spanning_set, aut_group, apply_perm
from symmetry import enumerate_group
from collections import Counter
from itertools import combinations
n = 36
G = read_code36(8)
assert rank(G, n) == 18 and all(dot(a, b) == 0 for a in G for b in G)
words = span(G)
wd = weight_distribution(words, n)
print("Y8 weight distribution", {i: c for i, c in enumerate(wd) if c})
assert (1 << n) - 1 in set(words)
S, w = low_weight_spanning_set(G, n)
print("words of weight <=", w, "span; count", len(S))
order, gens = aut_group(S, n)
print("|Aut| =", order, "gens", len(gens))
grp = enumerate_group(gens, n)
assert len(grp) == order
pickle.dump({"grp": grp, "gens": [tuple(g) for g in gens]}, open("<HOME>/c72_indep/y8/out/aut8.pkl", "wb"))
par = list(range(n))
def find(a):
    while par[a] != a: a = par[a]
    return a
for p in gens:
    for i in range(n):
        a, b = find(i), find(p[i])
        if a != b: par[a] = b
orb = {}
for i in range(n): orb.setdefault(find(i), []).append(i)
orbs = sorted(orb.values(), key=len)
print("coordinate orbits:", [len(o) for o in orbs], orbs)
W8 = [v for v in words if wt(v) == 8]
print("dim span w8:", rank(W8, n))
c = Counter(wt(a & b) for a in W8 for b in W8 if a != b)
print("w8 pairwise intersections:", dict(c))
masks = [sum(1 << i for i in o) for o in orbs]
for w_ in (8, 10, 12):
    cc = Counter(tuple(wt(v & m) for m in masks) for v in words if wt(v) == w_)
    print("weight", w_, "orbit-intersection types:", sorted(cc.items()))
# subcodes supported on unions of orbits
k = len(orbs)
for r in range(1, k + 1):
    for comb in combinations(range(k), r):
        m = sum(masks[i] for i in comb)
        sub = [v for v in words if v and v & ~m == 0]
        if sub:
            d = rank(sub, n)
            wd2 = weight_distribution([0] + sub, n)
            print("support on orbits", comb, "size", wt(m), "subcode dim", d, {i: c for i, c in enumerate(wd2) if c and i})
# word orbits under G
def word_orbits(Ws):
    Wset = {v: i for i, v in enumerate(Ws)}
    par = list(range(len(Ws)))
    def f(a):
        while par[a] != a: a = par[a]
        return a
    for p in gens:
        for i, v in enumerate(Ws):
            j = Wset[apply_perm(v, p, n)]
            a, b = f(i), f(j)
            if a != b: par[a] = b
    o = {}
    for i in range(len(Ws)): o.setdefault(f(i), []).append(i)
    return sorted(len(x) for x in o.values())
for w_ in (8, 10, 12):
    print("weight", w_, "word orbits:", word_orbits([v for v in words if wt(v) == w_]))
