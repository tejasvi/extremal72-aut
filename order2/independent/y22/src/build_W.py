"""Pick m functionals B(a_i, b_i) (each 1-dim mod X, translated by K) and measure on sample X-reps how often the
K-action on W is free (all 8 translation vectors distinct)."""
import sys, pickle, random, struct
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from autgroup import apply_perm
from symmetry import write_action
from linalg import Elim
P = Problem(read_code36(22), 36, 16)
FS = P.FS
A = pickle.load(open("<HOME>/c72_indep/y22/out/aut.pkl", "rb")); grp = A["grp"]
Kidx = pickle.load(open("<HOME>/c72_indep/y22/out/kernel_K.pkl", "rb"))
K = [grp[g] for g in Kidx]
cands = pickle.load(open("<HOME>/c72_indep/y22/out/W_candidates.pkl", "rb"))
pk = pickle.load(open("<HOME>/c72_indep/y22/out/sep_I28b_prep.pkl", "rb"))
sel = pk["sel"]
m = int(sys.argv[1])
# greedy: add (a, b0) pairs that are independent mod X + chosen
E = Elim()
for f, c in P.diag: E.add(f, 0)
for a, c in sel: E.add(FS.functional(a, c), 0)
Wp = []
seen_b = set()
for (dW, w, b0, a, Wl) in cands:
    if b0 in seen_b: continue
    if E.add(FS.functional(a, b0), 0)[0]:
        Wp.append((a, b0)); seen_b.add(b0)
    if len(Wp) == m: break
print("W pairs:", [("%x" % a, "%x" % b) for a, b in Wp])
xp = list(sel) + Wp
write_action(P, xp, K, "<HOME>/c72_indep/y22/out/xactionK_W%d.bin" % m)
data = open("<HOME>/c72_indep/y22/out/xactionK_W%d.bin" % m, "rb").read()
ng, nx = struct.unpack("<ii", data[:8])
maps = []
off = 8
for g in range(ng):
    vals = struct.unpack("<%dQ" % (nx + 1), data[off:off + (nx + 1) * 8]); off += (nx + 1) * 8
    maps.append((vals[:nx], vals[nx]))
def img(mp, x):
    rows, c = mp
    out = c
    for i, r in enumerate(rows):
        out ^= (bin(r & x).count("1") & 1) << i
    return out
nX = len(sel)
reps = [int(l.split()[1], 16) for l in open("<HOME>/c72_indep/y22/out/xreps22.txt")]
random.seed(3)
samp = random.sample(reps, 2000)
free = 0
hist = {}
for x in samp:
    # K acts on (x, w); translation vector for k: image(x, 0) >> nX
    vecs = set()
    for mp in maps:
        y = img(mp, x)
        assert y & ((1 << nX) - 1) == x, "K moves X?"
        vecs.add(y >> nX)
    hist[len(vecs)] = hist.get(len(vecs), 0) + 1
print("K-orbit size of w-translations over 2000 sample reps:", hist)
pickle.dump({"Wp": Wp, "xp": xp}, open("<HOME>/c72_indep/y22/out/W%d.pkl" % m, "wb"))
