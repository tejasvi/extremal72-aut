"""Generic engine data with a cross-subcode separator first.
usage: prep_generic.py K DIR SEPFILE TAG
SEPFILE (python literal): {"pairs": [[A_mask, C_mask], ...], "block_words": optional list of word lists (orders of
blocks after X; default: all w8 words inside some A_i or C_i), "first": optional list of words}
X = span{B(a, c) : a in basis Y(A_i), c in basis Y(C_i)} (pairs in order; dependent functionals skipped).
After X: greedy (min new dims, ties by weight) over the block words, then all remaining words by weight."""
import sys, pickle, time, ast
K = int(sys.argv[1]); DIR = sys.argv[2]; SEPFILE = sys.argv[3]; TAG = sys.argv[4]
sys.path.insert(0, DIR + "/src")
from problem import *
from engine_prep import *
from linalg import Elim
t0 = time.time()
P = Problem(read_code36(K), 36, 16)
FS = P.FS
spec = ast.literal_eval(open(SEPFILE).read())
def subcode_basis(T):
    return rref([v for v in P.words if v and v & ~T == 0], 36)
Xpairs = []
for A, C in spec.get("pairs", []):
    BA, BC = subcode_basis(A), subcode_basis(C)
    assert A & C == 0
    Xpairs += [(a, c) for a in BA for c in BC]
for a, c in spec.get("xpairs", []):
    assert a & c == 0 and a in P.wordset and c in P.wordset
    Xpairs.append((a, c))
E = Elim()
for f, c in P.diag: E.add(f, 0)
sel = []
for (a, c) in Xpairs:
    if E.add(FS.functional(a, c), 0)[0]:
        sel.append((a, c))
Xc = [FS.functional(a, c) for a, c in sel]
print("separator: %d candidate functionals, %d independent" % (len(Xpairs), len(sel)))
funcs = {y: [FS.functional(y, x) for x in P.shortened_basis(y)] for y in P.low}
def newdims(E, y):
    tmp = Elim(); tmp.rows = dict(E.rows)
    return sum(tmp.add(f, 0)[0] for f in funcs[y])
def greedy(E, words):
    o, rem = [], list(words)
    while rem:
        y = min(rem, key=lambda y: (newdims(E, y), wt(y), y))
        for f in funcs[y]: E.add(f, 0)
        o.append(y); rem.remove(y)
    return o
if "block_words" in spec:
    blocks = spec["block_words"]
else:
    masks = [m for pr in spec.get("pairs", []) for m in pr] + spec.get("block_masks", [])
    blocks = [[y for y in P.low if wt(y) == 8 and any(y & ~m == 0 for m in masks)]]
order = []
for y in spec.get("first", []):
    for f in funcs[y]: E.add(f, 0)
    order.append(y)
for blk in blocks:
    order += greedy(E, [y for y in blk if y not in set(order)])
seen = set(order)
order += sorted([y for y in P.low if y not in seen], key=lambda y: (wt(y), y))
ED = EngineData(P, order, extra_var_funcs=Xc)
out = DIR + "/out/%s.eng" % TAG
ED.write(out)
fd = {}
for y, d in zip(ED.words, ED.full_depth): fd.setdefault(d, []).append(wt(y))
print(TAG, "nv", ED.nv, "nX", len(sel), "events", len(ED.events), "time %.1f" % (time.time() - t0))
print("full depth -> #w8:", [(d, sum(1 for w in fd[d] if w == 8)) for d in sorted(fd) if any(w == 8 for w in fd[d])][:40])
pickle.dump({"order": order, "var_funcs": ED.var_funcs, "words": ED.words, "full_depth": ED.full_depth,
             "nX": len(sel), "sel": sel, "spec": spec}, open(out.replace(".eng", "_prep.pkl"), "wb"))
