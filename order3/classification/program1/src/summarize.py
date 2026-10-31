"""Summarize frames outputs: distinct class keys (Mon x conj), |Aut_Mon| distribution, A_d values, mass.
Usage: summarize.py n d out1 [out2 ...]
Output line format of frames: classkey autMon A_d selfconj gen ebindex"""
import sys, collections
from math import factorial
n, d = int(sys.argv[1]), int(sys.argv[2])
cls = {}
nlines = 0
for fn in sys.argv[3:]:
    for line in open(fn):
        p = line.split()
        if len(p) < 5: continue
        nlines += 1
        key, aut, ad, sc = p[0], int(p[1]), int(p[2]), int(p[3])
        if key in cls:
            if cls[key][:3] != (aut, ad, sc): print("INCONSISTENT", key[:16], cls[key][:3], (aut, ad, sc))
        else: cls[key] = (aut, ad, sc, None)
mon = 3**n * factorial(n)
mass_mon = sum((1 if sc else 2) * 3.0 / aut for aut, ad, sc, g in cls.values())   # sum over Mon classes of 3/|Aut|
nmon = sum(1 if sc else 2 for aut, ad, sc, g in cls.values())
print(f"n={n} d={d}: {nlines} output lines, {len(cls)} classes under Mon x conj, {nmon} under Mon")
print(f"  sum over Mon classes of 3/|Aut_Mon| = {mass_mon:.6g}")
print("  A_d values:", sorted(collections.Counter(ad for aut, ad, sc, g in cls.values()).items()))
print("  |Aut_Mon| distribution:", sorted(collections.Counter(aut for aut, ad, sc, g in cls.values()).items())[:40])
print("  self-conjugate classes:", sum(1 for v in cls.values() if v[2]))
