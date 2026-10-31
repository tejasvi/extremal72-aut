import sys
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from autgroup import *
n = 36
G = read_code36(39)
words = span(G)
W8 = [v for v in words if wt(v) == 8]
W10 = [v for v in words if wt(v) == 10]
W12 = [v for v in words if wt(v) == 12]
print("dim span w8:", rank(W8, n), " dim span w8+w10:", rank(W8 + W10, n), " dim span w12:", rank(W12, n))
S, w = low_weight_spanning_set(G, n)
order, gens = aut_group(S, n)
# coordinate orbits
par = list(range(n))
def find(a):
    while par[a] != a:
        par[a] = par[par[a]]; a = par[a]
    return a
for p in gens:
    for i in range(n):
        a, b = find(i), find(p[i])
        if a != b: par[a] = b
orb = {}
for i in range(n): orb.setdefault(find(i), []).append(i)
print("coordinate orbits:", sorted(len(o) for o in orb.values()), list(orb.values()))
def word_orbits(Ws):
    Wset = {v: i for i, v in enumerate(Ws)}
    par = list(range(len(Ws)))
    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for p in gens:
        for i, v in enumerate(Ws):
            j = Wset[apply_perm(v, p, n)]
            a, b = f(i), f(j)
            if a != b: par[a] = b
    o = {}
    for i in range(len(Ws)): o.setdefault(f(i), []).append(i)
    return sorted(len(x) for x in o.values())
print("w8 orbits:", word_orbits(W8))
print("w10 orbits:", word_orbits(W10))
print("w12 orbits:", word_orbits(W12))
# intersection numbers among weight-8 words
from collections import Counter
c = Counter()
for a in W8:
    for b in W8:
        if a != b: c[wt(a & b)] += 1
print("w8 pairwise intersections:", dict(c))
cov = Counter()
for v in W8:
    for i in range(n):
        if v >> i & 1: cov[i] += 1
print("w8 per coordinate:", sorted(cov.values()))
