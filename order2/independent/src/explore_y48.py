import sys, json, pickle
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from autgroup import low_weight_spanning_set, aut_group, apply_perm
from collections import Counter
d = json.load(open("<HOME>/c72_indep/out/control.json"))
Y = d["Y48"]; n = 24
words = span(Y)
S, w = low_weight_spanning_set(Y, n)
order, gens = aut_group(S, n)
print("|Aut|", order)
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
print("coordinate orbits", [len(o) for o in orb.values()])
W6 = [v for v in words if wt(v) == 6]
c = Counter(wt(a & b) for a in W6 for b in W6 if a != b)
print("w6 intersections", dict(c))
print("dim span w6", rank(W6, n))
# is there a partition into 4 disjoint w6 words (sextet-like)?
disj = [(a, b) for a in W6 for b in W6 if a < b and a & b == 0]
print("disjoint w6 pairs", len(disj))
