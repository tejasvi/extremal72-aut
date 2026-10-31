"""U-part structure: dims of span of syndromes of word sets mod X; find good chains in U."""
import sys, math, itertools
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from linalg import Elim
from y39_struct import *
P = Problem(read_code36(39), 36, 16)
S = structure(P.words)
FS = P.FS
Xc = [FS.functional(u, r) for u in S["Ub"] for r in S["Rb"]] + [FS.functional(h, S["vprime"]) for h in S["Hb"]]
base = Elim()
for f, c in P.diag: base.add(f, 0)
for f in Xc: base.add(f, 0)
nb = len(base)
funcs = {}
def syn(y):
    if y not in funcs:
        funcs[y] = [FS.functional(y, x) for x in P.shortened_basis(y)]
    return funcs[y]
def dims(words):
    E = Elim(); E.rows = dict(base.rows)
    for y in words:
        for f in syn(y): E.add(f, 0)
    return len(E) - nb
U8 = [y for y in S["U"] if wt(y) == 8]
H8 = [y for y in S["H"] if wt(y) == 8]
print("U-part dims of all U8:", dims(U8), " of H8:", dims(H8))
# subcodes of H spanned by pairs/triples of H8 words: dims vs number of w8 words inside
def subcode_words(b):
    return [w for w in span(b) if w]
best = {}
import random
random.seed(1)
for trial in range(3000):
    k = random.choice([2, 3, 4])
    b = random.sample(H8, k)
    if rank(b, 36) < k: continue
    W = subcode_words(b)
    w8 = [w for w in W if wt(w) == 8]
    d = dims(w8)
    key = (k, len(w8))
    if key not in best or d < best[key][0]:
        best[key] = (d, b)
for key in sorted(best):
    print("subcode dim", key[0], "#w8", key[1], "min U-part dims", best[key][0])
