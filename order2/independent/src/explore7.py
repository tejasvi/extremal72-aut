import sys
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from autgroup import *
n = 36
G = read_code36(39)
S, w = low_weight_spanning_set(G, n)
order, gens = aut_group(S, n)
# enumerate the whole group as tuples
def compose(p, q):  # first q then p? we use (p*q)[i] = p[q[i]]
    return tuple(p[q[i]] for i in range(n))
idp = tuple(range(n))
grp = {idp}
frontier = [idp]
gens_t = [tuple(g) for g in gens]
while frontier:
    nf = []
    for h in frontier:
        for g in gens_t:
            x = compose(g, h)
            if x not in grp:
                grp.add(x); nf.append(x)
    frontier = nf
print("group size", len(grp))
O16 = [0, 1, 2, 6, 15, 17, 18, 23, 27, 29, 30, 31, 32, 33, 34, 35]
O2 = [3, 28]
O18 = [4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19, 20, 21, 22, 24, 25, 26]
def restr(p, O): return tuple(p[i] for i in O)
for name, O in (("O18", O18), ("O16", O16), ("O2", O2)):
    imgs = {restr(p, O) for p in grp}
    ker = [p for p in grp if all(p[i] == i for i in O)]
    print(name, "image order", len(imgs), "kernel order", len(ker))
k18_16 = [p for p in grp if all(p[i] == i for i in O18 + O2)]
k16_18 = [p for p in grp if all(p[i] == i for i in O16 + O2)]
print("pointwise stabilizer of O18+O2:", len(k18_16), " of O16+O2:", len(k16_18))
# blocks of O18: find the 6 blocks of 3 (triples where every H-word meets in 0 or 2)
words = span(G)
H = [v for v in words if v and v & ~sum(1 << i for i in O18) == 0]
from itertools import combinations
blocks = []
for a, b, c in combinations(O18, 3):
    m = (1 << a) | (1 << b) | (1 << c)
    if all(wt(v & m) in (0, 2) for v in H):
        blocks.append((a, b, c))
print("H-blocks:", blocks)
import pickle
pickle.dump(sorted(grp), open("<HOME>/c72_indep/out/aut39.pkl", "wb"))
