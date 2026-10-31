"""State hashing check: at level t the subtree of a node depends on its assignment x (vars of levels < t) only via
the base syndromes of the constraints of levels >= t, i.e. via the projection of x onto the span of their
low parts.  If that span has rank < F_t, nodes merge 2^(F_t - rank) to 1 (exact caching).  Also reports the rank
for the constraints of levels t, t+1 only (near-future state)."""
import sys
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *
I = read_inst(sys.argv[1], meta=False); cons = I['cons']; vs = I['vstart']
for t in range(1, I['NLEV']):
    low = (1 << vs[t]) - 1
    b = Basis(); bn = Basis()
    for c in cons:
        if c['lv'] >= t:
            for f in c['forms']:
                b.add(f & low)
                if c['lv'] <= t + 1: bn.add(f & low)
    print(f"t={t:2d} F_t={vs[t]:3d} rank(all future low parts)={len(b):3d} rank(levels t,t+1)={len(bn):3d}")
