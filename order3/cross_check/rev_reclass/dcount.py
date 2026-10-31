from fractions import Fraction
from math import factorial
G = factorial(8) * 3
lhs = Fraction(0); n = 0; mon = 0; mass = Fraction(0)
for line in open('grp.txt'):
    aut, a8, sc, c = map(int, line.split())
    w = 1 if sc else 2
    assert a8 % 3 == 0
    lhs += Fraction(c * w * a8, 3 * aut); n += c; mon += c * w; mass += Fraction(c * w * 3, aut)
rhs = Fraction(0); neb = 0; ids = set(); monb = 0
for line in open('../../classification/program2/full/all.eb'):
    f = line.split(); assert f[0] == 'B'
    eid, aut, sc, nphi = int(f[1]), int(f[2]), int(f[3]), int(f[5])
    ids.add(eid); neb += 1; w = 1 if sc else 2; monb += w
    rhs += Fraction(w * nphi, G * aut)
# E_B aut/sc in all.eb vs L5.txt
L5 = [l.split() for l in open('../../classification/program2/n24/L5.txt')]
bad = 0
for line in open('../../classification/program2/full/all.eb'):
    f = line.split(); eid = int(f[1])
    if (int(L5[eid][1]), int(L5[eid][2])) != (int(f[2]), int(f[3])): bad += 1
print('cls24 classes', n, 'Mon classes', mon, 'mass sum 3/|Aut| =', float(mass))
print('E_B lines', neb, 'distinct ids', len(ids), 'min', min(ids), 'max', max(ids), 'E_B Mon classes', monb, 'aut/sc mismatches vs L5:', bad)
print('LHS =', lhs, '=', float(lhs))
print('RHS =', rhs, '=', float(rhs))
print('equal:', lhs == rhs, ' equals claimed 526493209678523/322560:', lhs == Fraction(526493209678523, 322560))
