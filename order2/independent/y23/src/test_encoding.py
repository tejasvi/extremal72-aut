"""Verify an engine data file against direct computation:
(1) for random variable values v, every word's syndrome as encoded (const + parity(rows & v)) equals the direct
    syndrome (B(y, x_j))_j of the form reconstructed from v;
(2) every word has exactly one full-determination event (r = 0) whose dead set equals its forbidden set, at the
    depth after which no variable enters its syndrome; all other events' dead cosets are genuinely dead."""
import sys, struct, pickle, random
sys.path.insert(0, "<HOME>/c72_indep/y23/src")
from problem import *
from linalg import solve
eng, prep = sys.argv[1], sys.argv[2]
P = Problem(read_code36(int(sys.argv[3]) if len(sys.argv) > 3 else 8), 36, 16)
pk = pickle.load(open(prep, "rb"))
var_funcs, words = pk["var_funcs"], pk["words"]
data = open(eng, "rb").read()
assert data[:4] == b"Y39F"
nv, nw, ne = struct.unpack("<iii", data[4:16])
off = 16
W = []
for i in range(nw):
    m, c = struct.unpack("<iI", data[off:off + 8]); off += 8
    rows = []
    for j in range(m):
        lo, hi = struct.unpack("<QQ", data[off:off + 16]); off += 16
        rows.append(lo | (hi << 64))
    W.append((m, c, rows))
EV = []
for i in range(ne):
    d, w, r = struct.unpack("<iii", data[off:off + 12]); off += 12
    basis = list(struct.unpack("<%dI" % r, data[off:off + 4 * r])); off += 4 * r
    nb = max(1, (1 << W[w][0]) // 8)
    bm = data[off:off + nb]; off += nb
    dead = {t for t in range(1 << W[w][0]) if bm[t >> 3] >> (t & 7) & 1}
    EV.append((d, w, basis, dead))
assert off == len(data) and nv == len(var_funcs) and nw == len(words) == len(P.low)
xbs = [P.shortened_basis(y) for y in words]
forb = [P.forbidden_syndromes(y, xb) for y, xb in zip(words, xbs)]
random.seed(7)
for trial in range(3):
    v = random.getrandbits(nv)
    funcs = [f for f, c in P.diag] + var_funcs
    tg = [c for f, c in P.diag] + [(v >> i) & 1 for i in range(nv)]
    M = P.vec_to_gram(solve(funcs, tg))
    assert P.is_valid_form(M)
    bad = 0
    for wi, y in enumerate(words):
        m, c, rows = W[wi]
        s_eng = c ^ sum((bin(rows[j] & v).count("1") & 1) << j for j in range(m))
        s_dir = sum(P.B(M, y, x) << j for j, x in enumerate(xbs[wi]))
        bad += s_eng != s_dir
    print("trial", trial, "syndrome mismatches:", bad, "of", nw)
full = {}
for (d, w, basis, dead) in EV:
    if not basis:
        full.setdefault(w, []).append((d, dead))
ok_full = all(len(full.get(w, [])) == 1 and full[w][0][1] == forb[w] for w in range(nw))
depth_ok = all(full[w][0][0] == max([i + 1 for i in range(nv) for j in range(W[w][0]) if W[w][2][j] >> i & 1] + [0]) for w in range(nw))
print("each word: one r=0 event with dead set == forbidden set:", ok_full, "; at full-determination depth:", depth_ok)
# genuine deadness of partial events (sampled): every element of a dead coset is forbidden
random.seed(3)
nbad = 0
sample = random.sample(EV, min(3000, len(EV)))
for (d, w, basis, dead) in sample:
    if not basis: continue
    from itertools import product
    for t in dead:
        for coeffs in product((0, 1), repeat=len(basis)):
            s = t
            for cf, b in zip(coeffs, basis):
                if cf: s ^= b
            if s not in forb[w]: nbad += 1
print("partial events sampled:", sum(1 for e in sample if e[2]), "non-forbidden elements inside 'dead' cosets:", nbad)
