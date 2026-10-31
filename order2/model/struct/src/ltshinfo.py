"""Summarise an LTSH symmetry file against its instance: key words' levels, orbit words' levels (component 0),
and per level how many of the orbit syndromes are determined (comparisons available)."""
import sys
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import read_inst
I = read_inst(sys.argv[1], meta=False); cons = I['cons']
tok = open(sys.argv[2]).read().split(); p = 0
def nxt():
    global p; p += 1; return tok[p - 1]
tag = nxt(); r, m0, c0, nO, nS0, nG, ncls = [int(nxt()) for _ in range(7)]
keys = [(int(nxt()), int(nxt())) for _ in range(r)]
M = 1 << m0
canon = [int(nxt()) for _ in range(M)]; hh = [int(nxt()) for _ in range(M)]
for k in range(ncls):
    c, n = int(nxt()), int(nxt()); [nxt() for _ in range(n)]
[nxt() for _ in range(nS0 * nS0)]
uc = []
for u in range(nO):
    uc.append(int(nxt())); [nxt() for _ in range(m0)]; [nxt() for _ in range(nS0)]
print(f"r={r} |G|={nG} |orbit(k0)|={nO} |S0|={nS0} classes={ncls}")
print("key constraint levels:", [cons[c]['lv'] for c, m in keys], "weights", [cons[c]['wt'] for c, m in keys])
lv = sorted(cons[c]['lv'] for c in uc)
print("orbit word levels:", lv)
gt = []
if r > 1:
    for g in range(nG):
        row = []
        for i in range(1, r):
            gc = int(nxt()); [nxt() for _ in range(keys[i][1])]
            row.append(cons[gc]['lv'])
        gt.append(row)
    import collections
    for i in range(1, r):
        cnt = collections.Counter(max(gt[g][i-1], cons[keys[i][0]]['lv']) + 1 for g in range(nG))
        print(f"component {i}: trigger level distribution over g:", sorted(cnt.items()))
