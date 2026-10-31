import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
cs = parse_magma_codes(HERE + '/data/36-d8.magma')
res = []
for idx, (n, rows) in enumerate(cs):
    B = [row_to_int(r) for r in rows]
    rk = rank(B)
    so = all(dot(x, y) == 0 for x in B for y in B)
    wd = weight_distribution(B, n)
    d = min(i for i in range(1, n + 1) if wd[i] > 0)
    nz = {i: int(wd[i]) for i in range(n + 1) if wd[i]}
    res.append(dict(idx=idx + 1, rank=rk, selforth=so, d=d, wd=nz, basis=B))
    print(idx + 1, rk, so, d, nz)
json.dump(res, open(HERE + '/data/codes41.json', 'w'))
