import sys
from fractions import Fraction
R = '../../classification/program2/n24/'
def lev_list(k):
    out = []
    for line in open(R + 'L%d.txt' % k):
        f = line.split(); out.append((int(f[1]), int(f[2]), int(f[3]), int(f[4])))
    return out
def mass_file(fns):
    out = []
    for fn in fns:
        for line in open(fn):
            a, sc, nv, fs = map(int, line.split()); out.append((a, sc, nv, fs))
    return out
ms = {1: mass_file(['m_L1.txt']), 2: mass_file(['m_L2.txt']), 3: mass_file(['m_L3.txt']), 4: mass_file(['m_L4_0.txt', 'm_L4_1.txt'])}
# check level-0 -> 1: number of 1-dim codes = sum_{w even >= 8} C(16,w) 3^(w-1); compare with sum |Mon16|/aut
from math import comb, factorial
Mon16 = factorial(16) * 3**16
L1 = lev_list(1)
lhs = sum(Fraction((1 if sc else 2) * Mon16, a) for a, sc, _, _ in L1)
rhs = sum(comb(16, w) * 3**(w - 1) for w in range(8, 17, 2))
print('level 1: codes from list', lhs, ' direct count', rhs, ' equal', lhs == rhs)
for k in range(1, 5):
    Lk = lev_list(k); Lk1 = lev_list(k + 1)
    assert len(ms[k]) == len(Lk), (k, len(ms[k]), len(Lk))
    # ms[k] rows are in file order for k<4; for k=4 split into parts 0/2 and 1/2 (even/odd lines)
    if k == 4:
        a0 = mass_file(['m_L4_0.txt']); a1 = mass_file(['m_L4_1.txt'])
        rows = []
        for i in range(len(Lk)):
            rows.append(a0[i // 2] if i % 2 == 0 else a1[i // 2])
    else:
        rows = ms[k]
    for i, (a, sc, nv, fs) in enumerate(rows):
        assert (a, sc) == (Lk[i][0], Lk[i][1]), (k, i)
        assert nv % 3 == 0
    rhs = sum(Fraction((1 if sc else 2) * nv // 3, a) for a, sc, nv, fs in rows)
    nsub = (4**(k + 1) - 1) // 3
    lhs = sum(Fraction((1 if sc else 2) * nsub, a) for a, sc, _, _ in Lk1)
    print(f'level {k}->{k+1}: sum_[D{k+1}] {nsub}/|Aut| = {float(lhs):.9f}   sum_[D{k}] #ext/|Aut| = {float(rhs):.9f}   exact equal: {lhs == rhs}')
    if lhs != rhs: print('   diff', lhs - rhs)
