"""Structural objects of Y8 used for the separator and variable order (correctness does not depend on them;
the G-invariance of the separator span is verified computationally)."""
import sys
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from codes import *

O2 = [3, 33]
O6 = [4, 9, 12, 13, 18, 25]
O12 = [5, 6, 7, 8, 15, 16, 19, 24, 26, 30, 34, 35]
O16 = [0, 1, 2, 10, 11, 14, 17, 20, 21, 22, 23, 27, 28, 29, 31, 32]
O18 = sorted(O6 + O12)
m2 = sum(1 << i for i in O2); m6 = sum(1 << i for i in O6); m12 = sum(1 << i for i in O12)
m16 = sum(1 << i for i in O16); m18 = m6 | m12


def structure(words):
    wset = set(words)
    H = [v for v in words if v and v & ~m18 == 0]
    R = [v for v in words if v and v & ~m16 == 0]
    U = [v for v in words if v and v & ~(m18 | m2) == 0]
    V = [v for v in words if v and v & ~(m16 | m2) == 0]
    u0 = m18 | m2
    r0 = m16
    assert u0 in wset and r0 in wset
    def basis_from(cands, start=()):
        b = list(start)
        for c in sorted(cands, key=lambda v: (wt(v), v)):
            if rank(b + [c], 36) > len(b):
                b.append(c)
        return b
    Hb = basis_from(H)
    Rb = basis_from(R, [r0])
    Ub = [u0] + Hb
    vprime = sorted([v for v in V if wt(v) == 8 and v & m2])[0]
    Vb = Rb + [vprime]
    assert len(Hb) == 6 and len(Rb) == 5 and rank(Ub, 36) == 7 and rank(Vb, 36) == 6
    return dict(H=H, R=R, U=U, V=V, Hb=Hb, Rb=Rb, Ub=Ub, Vb=Vb, u0=u0, r0=r0, vprime=vprime)
