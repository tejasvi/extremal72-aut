"""Structure of code K of codes36.txt: weights, Aut (pynauty), coordinate orbits, subcodes on orbit unions,
word orbits, and whether the Y39/Y8 skeleton (H=[18,6,8] 45+18, R=RM(1,4), U=H+u0 [20,7,8] 63+63+1, V=R+v')
exists as an Aut-invariant structure."""
import sys, pickle
K = int(sys.argv[1]); DIR = sys.argv[2]
sys.path.insert(0, DIR + "/src")
from codes import *
from autgroup import low_weight_spanning_set, aut_group, apply_perm
from symmetry import enumerate_group
from collections import Counter
from itertools import combinations
n = 36
G = read_code36(K)
assert rank(G, n) == 18 and all(dot(a, b) == 0 for a in G for b in G)
words = span(G)
wd = weight_distribution(words, n)
print("Y%d weight distribution" % K, {i: c for i, c in enumerate(wd) if c})
assert (1 << n) - 1 in set(words)
S, w = low_weight_spanning_set(G, n)
print("words of weight <=", w, "span; count", len(S))
order, gens = aut_group(S, n)
print("|Aut| =", order, "gens", len(gens))
grp = enumerate_group(gens, n)
assert len(grp) == order
pickle.dump({"grp": grp, "gens": [tuple(g) for g in gens]}, open(DIR + "/out/aut.pkl", "wb"))
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
orbs = sorted(orb.values(), key=lambda o: (len(o), o))
print("coordinate orbits:", [len(o) for o in orbs], orbs)
masks = [sum(1 << i for i in o) for o in orbs]
W8 = [v for v in words if wt(v) == 8]
print("dim span w8:", rank(W8, n))
for w_ in (8, 10, 12):
    cc = Counter(tuple(wt(v & m) for m in masks) for v in words if wt(v) == w_)
    print("weight", w_, "orbit-intersection types:", sorted(cc.items()) if len(cc) < 40 else ("%d types" % len(cc)))
k = len(orbs)
if k <= 10:
    for r in range(1, k + 1):
        for comb in combinations(range(k), r):
            m = sum(masks[i] for i in comb)
            sub = [v for v in words if v and v & ~m == 0]
            if sub and rank(sub, n) < 18:
                wd2 = weight_distribution([0] + sub, n)
                print("orbits", comb, "size", wt(m), "subcode dim", rank(sub, n), {i: c for i, c in enumerate(wd2) if c and i})
# skeleton search (not necessarily invariant): all RM(1,4)-like subcodes Y(T) with |T|=16, dim 5, 30 w8 words
# via supports of weight-16 words whose subcode is [16,5,8] with 30 words of weight 8
cand16 = [v for v in words if wt(v) == 16]
rm = []
for v in cand16:
    sub = [x for x in W8 if x & ~v == 0]
    if len(sub) == 30:
        rm.append(v)
print("weight-16 words t with 30 weight-8 words inside (RM(1,4) supports):", len(rm))
cand20 = [v for v in words if wt(v) == 20]
uu = []
for v in cand20:
    sub = [x for x in W8 if x & ~v == 0]
    if len(sub) == 63:
        uu.append(v)
print("weight-20 words with 63 weight-8 words inside (U-type supports):", len(uu))
pairs = [(t, u) for t in rm for u in uu if wt(t & u) == 0]
print("disjoint (RM support, U support) pairs:", len(pairs))
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
for w_ in (8,):
    print("weight", w_, "word orbits:", word_orbits([v for v in words if wt(v) == w_]))
pickle.dump({"orbs": orbs, "rm": rm, "uu": uu, "pairs": pairs}, open(DIR + "/out/structure.pkl", "wb"))
