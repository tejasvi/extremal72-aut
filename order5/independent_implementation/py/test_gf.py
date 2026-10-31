import sys, itertools, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gf import *

# field axioms
for a in range(16):
    for b in range(16):
        assert MUL[a][b] == MUL[b][a]
        for c in range(16):
            assert MUL[MUL[a][b]][c] == MUL[a][MUL[b][c]]
            assert MUL[a][b ^ c] == MUL[a][b] ^ MUL[a][c]
for a in range(1, 16):
    assert INV[a] and MUL[a][INV[a]] == 1
# multiplicative order of x (=2) is 5; the group is cyclic of order 15
def order(a):
    r, k = a, 1
    while r != 1:
        r = MUL[r][a]; k += 1
    return k
assert order(2) == 5, order(2)
assert any(order(a) == 15 for a in range(1, 16))
# conj: automorphism of order 2
for a in range(16):
    assert CONJ[CONJ[a]] == a
    for b in range(16):
        assert CONJ[a ^ b] == CONJ[a] ^ CONJ[b]
        assert CONJ[MUL[a][b]] == MUL[CONJ[a]][CONJ[b]]
assert any(CONJ[a] != a for a in range(16))
fixed = sorted(a for a in range(16) if CONJ[a] == a)
assert len(fixed) == 4 and fixed == GF4, (fixed, GF4)
# norm = y*conj(y) lands in GF(4); multiplicative
for a in range(16):
    assert NORM[a] == MUL[a][CONJ[a]]
    assert NORM[a] in GF4
    for b in range(16):
        assert NORM[MUL[a][b]] == MUL[NORM[a]][NORM[b]]
# each nonzero norm value has exactly 5 preimages
for n in GF4[1:]:
    assert sum(1 for a in range(16) if NORM[a] == n) == 5
assert sum(1 for y in range(16) if WT[y] == 4) == 5
assert sum(1 for y in range(16) if WT[y] == 2) == 10
assert MU5 == sorted(power(2, k) for k in range(5)), MU5
# Frobenius y->y^2 is an automorphism, commutes with conj, preserves weights
for a in range(16):
    s = MUL[a][a]
    assert WT[s] == WT[a]
    assert CONJ[s] == MUL[CONJ[a]][CONJ[a]]
# Fano lines: every pair in exactly one line
for i, j in itertools.combinations(range(7), 2):
    assert sum(1 for L in LINES if i in L and j in L) == 1
# x in P equals |S| mod 2 ; P is the [8,4,4] extended Hamming code (closed under symmetric difference with parity)
cw = set((S, x) for S, x in P)
for (S1, x1) in P:
    assert x1 == len(S1) % 2
    for (S2, x2) in P:
        assert (S1 ^ S2, x1 ^ x2) in cw
print("GF16 elements:", list(range(16)))
print("NORM:", NORM)
print("CONJ:", CONJ)
print("W =", W, "W2 =", W2, "MU5 =", MU5)
print("WT:", WT)
print("all unit tests passed")
