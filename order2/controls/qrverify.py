"""Verify control solutions: every SOLUTION of the engine rebuilds a genuine doubly-even code with the right
minimum weight; the code's own assignment is among the solutions.  Usage: qrverify.py PREFIX LOG [maxcheck]"""
import sys, pickle
sys.path.insert(0, '<HOME>/c72/explore/src')
from qrctl import *
pre, log = sys.argv[1], sys.argv[2]; mx = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
D = pickle.load(open(pre + '.pkl', 'rb'))
L = D['L']; own = D['a']
p = 47 if 'qr48' in pre else 71
S = setup(p)
sols = [int(l.split()[1], 16) for l in open(log) if l.startswith('SOLUTION')]
print("solutions:", len(sols), " own assignment found:", own in set(sols), flush=True)
ok = 0; bad = 0; cnt = 0
for a in sols[:mx]:
    if check_assignment(L, a) != 0: bad += 1; continue
    dim, mw, de = rebuild_code(S, L, a)
    if dim == S['n'] // 2 and de and mw >= 12: ok += 1
    else: bad += 1
    cnt += 1
print(f"checked {cnt}: genuine (dim n/2, doubly-even, d>=12) {ok}, bad {bad}")
