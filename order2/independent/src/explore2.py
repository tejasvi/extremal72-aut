import sys
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from forms import *
n = 36
G = read_code36(39)
words = span(G)
ones = (1 << n) - 1
FS = FormSpace(G, n)
print("N =", FS.N)
# diag functionals: y.y + y.1 for y in basis
diag = [FS.functional(g, g) ^ FS.functional(g, ones) for g in G]
print("diag rank", rank(diag, FS.N))
# gauge: D_i(y,y') = y_i y'_i ; as a form, M_ab = sum_i (g_a)_i (g_b)_i
gauge = []
for i in range(n):
    M = 0
    for a in range(18):
        for b in range(a, 18):
            if (G[a] >> i & 1) and (G[b] >> i & 1):
                M |= 1 << FS.idx[a][b]
    gauge.append(M)
print("gauge rank", rank(gauge, FS.N))
W8 = [v for v in words if wt(v) == 8]
def disjoint_basis(y):
    # basis of Y_y = {x in Y: x & y == 0}: solve linear conditions x restricted to supp(y) = 0
    # use words list (2^18) -- fine for exploration
    return rref([x for x in words if x & y == 0], n)
import time
t = time.time()
Ybasis = {}
for y in W8:
    Ybasis[y] = rref([x for x in words if x & y == 0], n)
print("time", time.time() - t, "dims", set(len(b) for b in Ybasis.values()))
allf = list(diag)
for y in W8:
    allf += [FS.functional(y, x) for x in Ybasis[y]]
print("dim span(w8 syndromes + diag) =", rank(allf, FS.N), "-> mod diag:", rank(allf, FS.N) - 17)
