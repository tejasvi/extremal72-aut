from fractions import Fraction
G = 40320 * 3
own = {}; cf = {}
for fn in ['n22_p0.txt', 'n22_p1.txt']:
    for line in open(fn):
        f = line.split()
        if f[0] != 'A': continue
        own[f[1]] = (int(f[2]), int(f[3]), int(f[4])); cf.setdefault(f[5], set()).add(f[1])
rhs = Fraction(0); neb = 0
for fn in ['n22_p0.txt.eb', 'n22_p1.txt.eb']:
    for line in open(fn):
        f = line.split(); neb += 1
        rhs += Fraction((1 if int(f[3]) else 2) * int(f[5]), G * int(f[2]))
lhs = sum(Fraction((1 if sc else 2) * a8, 3 * aut) for aut, sc, a8 in own.values())
mon = sum(1 if sc else 2 for aut, sc, a8 in own.values())
print('E_B', neb, 'classes', len(own), 'cform keys', len(cf), 'Mon classes', mon)
print('LHS', lhs, 'RHS', rhs, 'equal', lhs == rhs, 'claimed', lhs == Fraction(602364737, 12096))
