"""Affine action of Stab(X) on all 119 engine variables of sep_A2, for given separator values X.
usage: stab_maps.py XLIST OUT_TXT OUT_PKL [NSAMPLE]
XLIST: lines "0 <x hex>" (as in the rep files).
For g in Aut(Y23), B^g(u, v) = B(gu, gv). For a form B with variable vector v, vars(B^g) = M_g v + c_g: well defined,
since the variables are gauge-invariant and the gauge space span{D_i} is Aut-invariant (D_i^g = D_{g^-1 i}).
Checks (asserted):
  * the X-part of the action equals xaction23.bin, for every element of Stab(X) and NSAMPLE random elements;
  * Stab(X) = {g : A_g X + c_g = X} is closed under composition of the full affine maps;
  * g preserving T:  rows H have no H' or glue components -> phi_g(h)  = h-part of B^g   (depends on x, h only);
                     rows H' have no H or glue components -> phi'_g(h') = h'-part of B^g;
  * g swapping T, T^c: rows H have no H or glue components -> psi_g(h') = h-part of B^g  (depends on x, h' only);
                     rows H' have no H' or glue components -> psi'_g(h) = h'-part of B^g.
Variables: X = 0..35, H = 36..69, H' = 70..103, glue = 104..118.
OUT_TXT per X: "X <x> <nh> <ns>", nh lines "P <const> <col_0> .. <col_33>" (phi), ns lines "S <const> <cols>" (psi),
all hex; h bit k = variable 36 + k, h' bit k = variable 70 + k."""
import sys, pickle, struct, random
DIR = "<HOME>/c72_indep/y23"
sys.path.insert(0, DIR + "/src")
from problem import *
from linalg import solve
from autgroup import apply_perm

XL, OUT_TXT, OUT_PKL = sys.argv[1], sys.argv[2], sys.argv[3]
NSAMPLE = int(sys.argv[4]) if len(sys.argv) > 4 else 200
T = 0x85c320ff3
FULL = (1 << 36) - 1
P = Problem(read_code36(23), 36, 16)
pk = pickle.load(open(DIR + "/out/sep_A2_prep.pkl", "rb"))
VF = pk["var_funcs"]
NV = len(VF)
assert NV == 119 and pk["nX"] == 36
XM = (1 << 36) - 1
HM = ((1 << 34) - 1) << 36
H2M = ((1 << 34) - 1) << 70
GM = ((1 << 15) - 1) << 104
A = pickle.load(open(DIR + "/out/aut.pkl", "rb"))
grp = A["grp"]

# action of the separator variables (xaction23.bin, written with perms = grp in this order)
raw = open(DIR + "/out/xaction23.bin", "rb").read()
ng, nx = struct.unpack_from("<II", raw, 0)
assert ng == len(grp) and nx == 36
xact = []
off = 8
for g in range(ng):
    rows = struct.unpack_from("<36Q", raw, off); off += 288
    c, = struct.unpack_from("<Q", raw, off); off += 8
    xact.append((rows, c))


def xapply(g, x):
    rows, c = xact[g]
    y = c
    for i in range(36):
        if bin(rows[i] & x).count("1") & 1:
            y |= 1 << i
    return y


# basis forms: v0 (diag constants, all variables 0) and homogeneous vk (diag 0, variable k = 1)
funcs = [f for f, c in P.diag] + VF
nd = len(P.diag)
v0 = solve(funcs, [c for f, c in P.diag] + [0] * NV)
vk = [solve(funcs, [0] * nd + [int(j == k) for j in range(NV)]) for k in range(NV)]
G0 = P.vec_to_gram(v0)
Gk = [P.vec_to_gram(v) for v in vk]
assert P.is_valid_form(G0)


def coords_rows(p):
    return [P.FS.coords(apply_perm(g, p, 36)) for g in P.G]


def image_gram(M, C):
    """Gram matrix of B^g in basis P.G: entry (i, j) = B(g G_i, g G_j) = C_i^T M C_j."""
    k = P.k
    R = []
    for i in range(k):
        r = 0
        ci = C[i]
        for a in range(k):
            if ci >> a & 1:
                r ^= M[a]
        R.append(r)
    out = [0] * k
    for i in range(k):
        for j in range(k):
            if bin(R[i] & C[j]).count("1") & 1:
                out[i] |= 1 << j
    return out


def varsof(M):
    v = P.gram_to_vec(M)
    return sum((bin(f & v).count("1") & 1) << i for i, f in enumerate(VF))


def full_action(p):
    """(cols, c): vars(B^g) = c ^ XOR_{k: v_k = 1} cols[k]."""
    C = coords_rows(p)
    c = varsof(image_gram(G0, C))
    cols = [varsof(image_gram(M, C)) for M in Gk]
    return cols, c


def apply_full(act, v):
    cols, c = act
    y = c
    k = 0
    while v:
        if v & 1:
            y ^= cols[k]
        v >>= 1
        k += 1
    return y


def check_xpart(g, act):
    cols, c = act
    rows, xc = xact[g]
    for k in range(36, NV):
        assert cols[k] & XM == 0, "X-part depends on a non-separator variable"
    assert c & XM == xc, "constant differs from xaction"
    for j in range(36):
        colx = sum(((rows[i] >> j) & 1) << i for i in range(36))
        assert cols[j] & XM == colx, "column differs from xaction"


random.seed(12345)
for g in random.sample(range(ng), NSAMPLE):
    check_xpart(g, full_action(grp[g]))
print("X-part of the full action = xaction23.bin on %d random elements" % NSAMPLE)


def sub(v, mask, sh):
    return (v & mask) >> sh


xs = [int(l.split()[1], 16) for l in open(XL) if l.strip()]
outl = []
store = {}
for x in xs:
    stab = [g for g in range(ng) if xapply(g, x) == x]
    acts = {g: full_action(grp[g]) for g in stab}
    for g in stab:
        check_xpart(g, acts[g])
    # closure of the full affine maps
    key = {g: (tuple(acts[g][0]), acts[g][1]) for g in stab}
    keyset = set(key.values())
    assert len(keyset) == len(stab), "action not faithful on the stabilizer"
    pairs = [(a, b) for a in stab for b in stab]
    if len(pairs) > 3000:
        pairs = random.sample(pairs, 3000)
    for a, b in pairs:
        ca, cb = acts[a], acts[b]
        comp = (tuple(apply_full(ca, cb[0][k]) ^ ca[1] for k in range(NV)), apply_full(ca, cb[1]))
        assert comp in keyset, "stabilizer maps not closed under composition"
    xv = x
    phis, psis, phi2s, psi2s = [], [], [], []
    for g in stab:
        cols, c = acts[g]
        cx = apply_full((cols, c), xv)          # image of (x, 0, 0, 0): constants incl. the x-dependent part
        assert cx & XM == x
        img = apply_perm(T, grp[g], 36)
        if img == T:
            for k in list(range(70, 104)) + list(range(104, NV)):
                assert cols[k] & HM == 0, "h-part depends on h' or glue for a T-preserving element"
            for k in list(range(36, 70)) + list(range(104, NV)):
                assert cols[k] & H2M == 0, "h'-part depends on h or glue for a T-preserving element"
            phis.append((sub(cx, HM, 36), [sub(cols[k], HM, 36) for k in range(36, 70)]))
            phi2s.append((sub(cx, H2M, 70), [sub(cols[k], H2M, 70) for k in range(70, 104)]))
        else:
            assert img == FULL ^ T, "element neither preserves nor swaps the halves"
            for k in list(range(36, 70)) + list(range(104, NV)):
                assert cols[k] & HM == 0, "h-part depends on h or glue for a swapping element"
            for k in list(range(70, 104)) + list(range(104, NV)):
                assert cols[k] & H2M == 0, "h'-part depends on h' or glue for a swapping element"
            psis.append((sub(cx, HM, 36), [sub(cols[k], HM, 36) for k in range(70, 104)]))
            psi2s.append((sub(cx, H2M, 70), [sub(cols[k], H2M, 70) for k in range(36, 70)]))
    print("X %x: |Stab| = %d, T-preserving %d, swapping %d" % (x, len(stab), len(phis), len(psis)))
    outl.append("X %x %d %d" % (x, len(phis), len(psis)))
    for c, cols in phis:
        outl.append("P %x " % c + " ".join("%x" % v for v in cols))
    for c, cols in psis:
        outl.append("S %x " % c + " ".join("%x" % v for v in cols))
    store[x] = {"stab": stab, "phi": phis, "phi2": phi2s, "psi": psis, "psi2": psi2s}
open(OUT_TXT, "w").write("\n".join(outl) + "\n")
pickle.dump(store, open(OUT_PKL, "wb"))
print("wrote", OUT_TXT, OUT_PKL)
