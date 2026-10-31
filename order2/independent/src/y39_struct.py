"""Structural objects of Y39 used for the variable order (not needed for correctness)."""
import sys
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *

O16 = [0, 1, 2, 6, 15, 17, 18, 23, 27, 29, 30, 31, 32, 33, 34, 35]
O2 = [3, 28]
O18 = [4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19, 20, 21, 22, 24, 25, 26]
m16 = sum(1 << i for i in O16); m2 = sum(1 << i for i in O2); m18 = sum(1 << i for i in O18)


def structure(words):
    H = [v for v in words if v and v & ~m18 == 0]
    R = [v for v in words if v and v & ~m16 == 0]
    U = [v for v in words if v and v & ~(m18 | m2) == 0]
    V = [v for v in words if v and v & ~(m16 | m2) == 0]
    Hb = rref(H, 36)
    Hb = [min(H, key=wt)] if False else Hb
    u0 = m18 | m2
    r0 = m16
    assert u0 in set(words) and r0 in set(words)
    # bases made of nice vectors: H basis from weight-8 words, R basis r0 + weight-8 words
    def basis_from(cands, start=()):
        b = list(start)
        for c in sorted(cands, key=lambda v: (wt(v), v)):
            if rank(b + [c], 36) > len(b):
                b.append(c)
        return b
    Hb = basis_from(H)
    Rb = basis_from(R, [r0])
    Ub = [u0] + Hb
    vprime = sorted([v for v in V if wt(v) == 8 and v & m2], key=lambda v: v)[0]
    Vb = Rb + [vprime]
    assert len(Hb) == 6 and len(Rb) == 5 and rank(Ub, 36) == 7 and rank(Vb, 36) == 6
    return dict(H=H, R=R, U=U, V=V, Hb=Hb, Rb=Rb, Ub=Ub, Vb=Vb, u0=u0, r0=r0, vprime=vprime)
