# exact level chain for the E_B classification with OWN extension counts (src/ebext.c)
from fractions import Fraction
from math import comb, factorial
D = '../ebchk/'
L = '../../classification/program1/eb/n24.L%d.txt'
def ext(fn):
    out = []
    for line in open(fn):
        a, sc, nv = line.split(); out.append((int(a.replace('x2', '')), int(sc), int(nv)))
    return out
def lst(k):
    out = []
    for line in open(L % k):
        f = line.split(); a = f[2]; out.append((int(a.replace('x2', '')), 0 if 'x2' in a else 1))
    return out
Mon16 = factorial(16) * 3**16
E = {1: ext(D + 'L1.ext'), 2: ext(D + 'L2.ext'), 3: ext(D + 'L3.ext'), 4: ext(D + 'L4.ext')}
# level 0 -> 1
lhs = sum(Fraction((1 if sc else 2) * Mon16, a) for a, sc, _ in E[1])
rhs = sum(comb(16, w) * 3**(w - 1) for w in range(8, 17, 2))
print('level 0->1: sum |Mon16|/|Aut| =', lhs, ' direct count =', rhs, ' equal:', lhs == rhs)
for k in range(1, 5):
    nxt = lst(k + 1) if k >= 1 else None
    if k + 1 in E: nxt = [(a, sc) for a, sc, _ in E[k + 1]]
    if k >= 2:
        assert [(a, sc) for a, sc, _ in E[k]] == lst(k), 'aut/sc of ext file differs from list at level %d' % k
    nsub = (4**(k + 1) - 1) // 3
    lhs = sum(Fraction((1 if sc else 2) * nsub, a) for a, sc in nxt)
    for a, sc, nv in E[k]: assert nv % 3 == 0
    rhs = sum(Fraction((1 if sc else 2) * (nv // 3), a) for a, sc, nv in E[k])
    print(f'level {k}->{k+1}: classes {len(E[k])} -> {len(nxt)}; sum_[D{k+1}] {nsub}/|Aut| = {lhs} ({float(lhs):.9f}); '
          f'sum_[D{k}] ext/|Aut| = {rhs} ({float(rhs):.9f}); exact equal: {lhs == rhs}')
