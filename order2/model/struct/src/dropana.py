"""For a flag instance: at each level t, S = constraints with lv < t (words checkable at level t).
Greedy drop: repeatedly remove the word y in S maximizing (dims saved u(y)) - L_y while > 0, where
u(y) = dim Sigma(S) - dim Sigma(S minus y), Sigma = span of syndrome forms; after dropping, words whose forms
are still in Sigma(S') remain checkable (free riders are re-added).  Reports the improved log2 N at each level."""
import sys, math
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *
I = read_inst(sys.argv[1]); T = int(sys.argv[2]) if len(sys.argv) > 2 else I['NLEV']
cons = I['cons']; vs = I['vstart']
for c in cons: c['L'] = -math.log2(pass_prob(c)[0])
def span(words):
    b = Basis()
    for c in words:
        for f in c['forms']: b.add(f)
    return b
def inspan(b, c): return all(b.reduce(f) == 0 for f in c['forms'])
for t in range(1, T + 1):
    S = [c for c in cons if c['lv'] < t]
    if not S: continue
    b = span(S); F = len(b); L = sum(c['L'] for c in S)
    assert F == vs[t], (F, vs[t])
    cur = list(S); curF = F; curL = L; dropped = []
    while True:
        best = None
        for i, y in enumerate(cur):
            rest = cur[:i] + cur[i+1:]
            b2 = span(rest); F2 = len(b2)
            if F2 == curF: continue
            # free riders: y itself may still be in span
            L2 = sum(c['L'] for c in rest) + (y['L'] if inspan(b2, y) else 0)
            gain = (curF - F2) - (curL - L2)
            if best is None or gain > best[0]: best = (gain, i, F2, L2)
        if best is None or best[0] <= 1e-9: break
        g, i, F2, L2 = best
        dropped.append((cur[i]['wt'], curF - F2, round(cur[i]['L'], 2)))
        cur = cur[:i] + cur[i+1:]; curF = F2; curL = L2
    print(f"t={t} words {len(S)} F {F} L {L:.1f} ln {F-L:.1f} | after drops: words {len(cur)} F {curF} L {curL:.1f} ln {curF-curL:.1f} gain {(F-L)-(curF-curL):.1f} dropped {dropped[:12]}{'...' if len(dropped)>12 else ''}", flush=True)
