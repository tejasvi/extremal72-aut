"""Summary of rglue output files (small runs): own class count, cform key count, consistency between the two
canonical forms, Mon count, mass, and the weighted double count
    sum_{E Mon classes} (A_D/3)/|Aut(E)|  ==  sum_{E_B Mon classes} N_phi(E_B) / (|G| |Aut(E_B)|),  |G| = D! * 3.
usage: python3 -I rsum.py D OUT1 [OUT2 ...]      (reads OUTi and OUTi.eb)"""
import sys
from fractions import Fraction
from math import factorial
D = int(sys.argv[1]); G = factorial(D) * 3
mine = {}; cf = {}; bad = 0; nacc_lines = 0
rhs = Fraction(0); nphi_tot = 0; leaves = 0; acc = 0; dist = 0; secs = 0.0; neb = 0
for fn in sys.argv[2:]:
    for line in open(fn):
        f = line.split()
        if f[0] != 'A': continue
        nacc_lines += 1
        myh, myaut, mysc, ad, key, cfaut, cfsc = f[1], int(f[2]), int(f[3]), int(f[4]), f[5], int(f[6]), int(f[7])
        rec = (key, myaut, mysc, ad, cfaut, cfsc)
        if myh in mine and mine[myh] != rec: bad += 1
        mine[myh] = rec
        cf.setdefault(key, set()).add(myh)
    for line in open(fn + '.eb'):
        f = line.split()
        ebaut, ebsc, lv, nphi, a, d, s = int(f[2]), int(f[3]), int(f[4]), int(f[5]), int(f[6]), int(f[7]), float(f[9])
        w = 1 if ebsc else 2
        rhs += Fraction(w * nphi, G * ebaut); nphi_tot += nphi; leaves += lv; acc += a; dist += d; secs += s; neb += 1
lhs = Fraction(0); mon = 0; mass = Fraction(0); autmis = 0; scmis = 0
for myh, (key, myaut, mysc, ad, cfaut, cfsc) in mine.items():
    w = 1 if mysc else 2
    mon += w; mass += Fraction(3 * w, myaut); lhs += Fraction(w * ad, 3 * myaut)
    if myaut != cfaut: autmis += 1
    if mysc != cfsc: scmis += 1
multi = sum(1 for k, s in cf.items() if len(s) > 1)
print(f"E_B processed {neb}: leaves {leaves}, N_phi {nphi_tot}, accepted {acc}, distinct-per-E_B lines {nacc_lines}, cpu {secs:.1f}s")
print(f"own classes (Mon x conj) {len(mine)}, cform keys {len(cf)}, cform keys with >1 own key {multi}, own keys with inconsistent records {bad}")
print(f"aut mismatches (own vs cform) {autmis}, selfconj mismatches {scmis}")
print(f"Mon classes {mon}, mass sum 3/|Aut| = {float(mass):.6f}")
print(f"double count: LHS = {lhs} = {float(lhs):.9f}")
print(f"              RHS = {rhs} = {float(rhs):.9f}   equal: {lhs == rhs}")
from collections import Counter
print("aut histogram (own):", sorted(Counter(r[1] for r in mine.values()).items()))
print("A_D histogram:", sorted(Counter(r[3] for r in mine.values()).items()))
