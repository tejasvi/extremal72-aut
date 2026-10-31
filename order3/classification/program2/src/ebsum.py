"""Summary of an ebcls2 level file (deduplicated): classes, flag counts, mass sum (non-self-conjugate count twice).
usage: python3 -I ebsum.py FILE"""
import sys
from fractions import Fraction
from collections import Counter
n = 0; mon = 0; mass = Fraction(0); fs = 0; hall = 0; both = 0; auts = Counter()
for line in open(sys.argv[1]):
    f = line.split()
    aut, sc, a, h = int(f[1]), int(f[2]), int(f[3]), int(f[4])
    w = 1 if sc else 2
    n += 1; mon += w; mass += Fraction(w, aut); auts[aut] += 1
    fs += a; hall += h; both += a and h
print(f"classes (Mon x conj) {n}, Mon classes {mon}, full support {fs}, Hall {hall}, both {both}")
print(f"mass sum_Mon 1/|Aut| = {float(mass):.6f}")
print("aut histogram:", sorted(auts.items())[:40])
