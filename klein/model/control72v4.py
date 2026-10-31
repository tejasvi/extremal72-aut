"""Control for the C2 x C2 model at length 72 with d = 12: the extended QR code of length 72 (PSL(2,71) acts;
71 = 3 mod 4 so involutions are fixed-point-free and V4 acts freely).  Extract Y, bb and QR72's own form B, check
it satisfies every constraint of the model, export the instance for the C solver."""
import sys, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, HERE)
from v4sat import setup, applym, pc
from v4export import export
p = 71; N = 72; INF = 71
Q = set((x * x) % p for x in range(1, p))
def rank(vs):
    b = []
    for v in vs:
        for x in b: v = min(v, v ^ x)
        if v: b.append(v)
    return b
ext = None
for idem in (Q, set(range(1, p)) - Q, Q | {0}, (set(range(1, p)) - Q) | {0}):
    gens = []
    for s in range(p):
        w = 0
        for i in idem: w |= 1 << ((i + s) % p)
        gens.append(w)
    B = rank(gens)
    if len(B) == 36:
        e = [b | ((pc(b) & 1) << 71) for b in B]
        if all(pc(x) % 4 == 0 for x in e): ext = e; break
assert ext
def mobius(a, b, c, d):
    def f(x):
        if x == INF: return INF if c == 0 else (a * pow(c, p - 2, p)) % p
        den = (c * x + d) % p
        if den == 0: return INF
        return ((a * x + b) * pow(den, p - 2, p)) % p
    return [f(x) for x in range(72)]
alpha = mobius(0, p - 1, 1, 0)           # x -> -1/x
beta = None
for a in range(p):
    for b in range(1, p):
        dt = (-(a * a) - b * b) % p
        if dt == 0 or pow(dt, (p - 1) // 2, p) != 1: continue   # need det a nonzero square (PSL)
        m = mobius(a, b, b, (p - a) % p)
        if m != alpha and all(alpha[m[i]] == m[alpha[i]] for i in range(N)) and all(m[m[i]] == i for i in range(N)):
            beta = m; break
    if beta: break
assert beta and all(alpha[i] != i and beta[i] != i and alpha[beta[i]] != i for i in range(N))
Cb = rank(ext)
for g in (alpha, beta):
    assert len(rank(Cb + [applym(g, x, N) for x in Cb])) == 36
pairs = []; used = set()
for x in range(N):
    if x in used: continue
    y = beta[x]
    pairs.append((x, alpha[x])); pairs.append((y, alpha[y])); used |= {x, alpha[x], y, alpha[y]}
pidx = {}
for i, (a_, b_) in enumerate(pairs): pidx[a_] = (i, 0); pidx[b_] = (i, 1)
bb = [pidx[beta[pairs[i][0]]][0] for i in range(36)]
assert all(pidx[beta[pairs[i][0]]][1] == 0 and pidx[beta[pairs[i][1]]][1] == 1 for i in range(36))
def proj(w):
    y = 0; z = 0
    for i, (a_, b_) in enumerate(pairs):
        ai = (w >> a_) & 1; bi = (w >> b_) & 1
        if ai ^ bi: y |= 1 << i
        if ai: z |= 1 << i
    return y, z
# fixed subcode: kernel of c -> sum c_i (g_i + alpha g_i)
diffs = [g ^ applym(alpha, g, N) for g in Cb]
red = []; kern = []
for i, dv in enumerate(diffs):
    r = dv; c = 1 << i
    for (pr, pcc, bit) in red:
        if (r >> bit) & 1: r ^= pr; c ^= pcc
    if r == 0: kern.append(c)
    else: red.append((r, c, r.bit_length() - 1))
fixedw = []
for c in kern:
    v = 0
    for i in range(36):
        if (c >> i) & 1: v ^= Cb[i]
    fixedw.append(v)
Ygens = rank([proj(w)[1] for w in fixedw])
assert len(Ygens) == 18
S = setup(Ygens, bb, verbose=True, m=36, d=12)
basis = S['basis']; E = S['E']; ei = S['ei']; K = 18
# QR72's own B: z-part of a codeword whose pair-sum pattern is b_k
imgs = [proj(g) for g in Cb]
redl = []
for i, (y, z) in enumerate(imgs):
    r = y; c = 1 << i
    for (pr, pcc, bit) in redl:
        if (r >> bit) & 1: r ^= pr; c ^= pcc
    if r: redl.append((r, c, r.bit_length() - 1))
def preimage(y):
    r = y; c = 0
    for (pr, pcc, bit) in redl:
        if (r >> bit) & 1: r ^= pr; c ^= pcc
    assert r == 0
    v = 0
    for i in range(36):
        if (c >> i) & 1: v ^= Cb[i]
    return v
zb = [proj(preimage(basis[k]))[1] for k in range(K)]
Bq = {(i, j): pc(zb[i] & basis[j]) & 1 for (i, j) in E}
assert all(Bq[(min(i, j), max(i, j))] == pc(zb[j] & basis[i]) & 1 for (i, j) in E), "B not symmetric"
diag_ok = all(Bq[(k, k)] == ((pc(basis[k]) // 2) + Bq[(0, k)]) % 2 for k in range(1, K))
coef = S['coef']
def Bval(x, y):
    cx = coef[x]; cy = coef[y]; s = 0
    for i in range(K):
        if (cx >> i) & 1:
            for j in range(K):
                if (cy >> j) & 1: s ^= Bq[(min(i, j), max(i, j))]
    return s
inv_ok = all(Bval(applym(bb, basis[i], 36), applym(bb, basis[j], 36)) == Bq[(i, j)] for (i, j) in E)
vec = 0
for (i, j), v in Bq.items():
    if v: vec |= 1 << ei(i, j)
def redv(v, piv):
    for c in sorted(piv, reverse=True):
        if (v >> c) & 1: v ^= piv[c]
    return v
piv = {}
for w_ in S['W']:
    r = redv(w_, piv)
    if r: piv[r.bit_length() - 1] = r
seen = set()
for x in range(36):
    if x in seen: continue
    R = (1 << x) | (1 << bb[x]); seen |= {x, bb[x]}
    dlt = 0
    for (i, j) in E:
        if pc(basis[i] & basis[j] & R) & 1: dlt |= 1 << ei(i, j)
    r = redv(dlt, piv)
    if r: piv[r.bit_length() - 1] = r
mem_ok = redv(vec ^ S['part'], piv) == 0
print(f"QR72 own B: symmetric, diagonal ok {diag_ok}, bb-invariant {inv_ok}, in valid affine space mod swaps {mem_ok}")
export(S, HERE + '/inst/qr72_d12.txt')
pickle.dump(dict(W=S['W'], part=S['part'], E=E, basis=basis, bb=bb, Ygens=Ygens), open(HERE + '/inst/qr72_d12.pkl', 'wb'))
print("exported")
