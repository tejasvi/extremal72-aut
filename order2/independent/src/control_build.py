"""Build QR48 (extended binary QR code, p = 47), a fixed-point-free involution x -> -1/x in PSL(2,47),
the contracted fixed code Y48 = pi(F_sigma), and QR48's own form B on Y48."""
import sys, json
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *

p = 47
INF = 47  # coordinate index of infinity
N = 48
Q = sorted({(x * x) % p for x in range(1, p)})
Nr = sorted(set(range(1, p)) - set(Q))
assert len(Q) == 23

def cyclic_span(supp):
    v = sum(1 << i for i in supp)
    shifts = []
    for s in range(p):
        shifts.append(sum(1 << ((i + s) % p) for i in supp))
    return rref(shifts, p)

best = None
for name, supp in (("Q", Q), ("N", Nr), ("Q0", [0] + Q), ("N0", [0] + Nr)):
    b = cyclic_span(supp)
    if len(b) == 24:
        words = span(b)
        d = min(wt(w) for w in words if w)
        print(name, "dim", len(b), "min weight", d)
        if d == 11 and best is None:
            best = (name, b)
name, b47 = best
# extend by parity at coordinate 47 (infinity)
ext = [v | ((wt(v) & 1) << INF) for v in b47]
words48 = span(ext)
wd = weight_distribution(words48, N)
print("QR48 from", name, "weight distribution", {i: c for i, c in enumerate(wd) if c})
assert min(i for i in range(1, N + 1) if wd[i]) == 12
for a in ext:
    for c in ext:
        assert dot(a, c) == 0
assert all(wt(w) % 4 == 0 for w in ext)
# involution x -> -1/x on the projective line (0 <-> inf)
def inv(x):
    if x == INF: return 0
    if x == 0: return INF
    return (-pow(x, p - 2, p)) % p
perm = [inv(x) for x in range(N)]
assert all(perm[perm[x]] == x and perm[x] != x for x in range(N))
def apply(v, pm):
    return sum(1 << pm[i] for i in range(N) if v >> i & 1)
W48 = set(words48)
assert all(apply(v, perm) in W48 for v in ext), "involution does not preserve the code"
print("x -> -1/x preserves QR48, fixed-point-free")
# pairs: (a_i, b_i) with a_i < b_i ; first coordinate of pair i = a_i (copy 0), second = b_i (copy 1)
pairs = sorted({(min(x, perm[x]), max(x, perm[x])) for x in range(N)})
assert len(pairs) == 24
# re-coordinatize: new bit i = old a_i, new bit 24+i = old b_i
def recoord(v):
    out = 0
    for i, (a, bb) in enumerate(pairs):
        if v >> a & 1: out |= 1 << i
        if v >> bb & 1: out |= 1 << (24 + i)
    return out
C = [recoord(v) for v in ext]
mask24 = (1 << 24) - 1
# fixed subcode: c with c0 == c1 ; contracted: c0
# compute as kernel of c -> c0 + c1 over the span
Cw = span(C)
F = [c for c in Cw if (c & mask24) == (c >> 24)]
Y48 = rref([c & mask24 for c in F], 24)
print("fixed subcode size", len(F), "contracted dim", len(Y48))
Yw = span(Y48)
wdY = weight_distribution(Yw, 24)
print("Y48 weight distribution", {i: c for i, c in enumerate(wdY) if c})
for a in Y48:
    for c in Y48:
        assert dot(a, c) == 0
assert len(Y48) == 12
# every codeword c of QR48 has c0 + c1 in Y48
Yset = set(Yw)
assert all(((c & mask24) ^ (c >> 24)) in Yset for c in C)
json.dump({"Y48": Y48, "QR48_recoord_basis": C, "pairs": pairs, "QR48_basis": ext, "built_from": name},
          open("<HOME>/c72_indep/out/control.json", "w"))
print("saved")
