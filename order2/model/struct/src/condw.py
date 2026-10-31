"""Conditional low-word weights for one search node (STRUCT direction 7: per-subtree flags).
Given an instance (with .meta), a node assignment (hex, as printed by lwe10n NODEOUT) and its level T (variables of
levels < T assigned), every constraint word y gets w_y = -log2 P(syndrome of y good | the assigned variables), where the
syndrome ranges uniformly over the reachable affine set s_fixed + Im(L_free).  This does not depend on how the free
variables are later ordered, so flagbeam4 can rank continuations of the flag for this subtree with these weights.
Output: lines 'y weight' (flagbeam4 LOWFILE format); words already fully determined get weight 0 (dead: 99).
Usage: condw.py INSTANCE ASGHEX T OUT"""
import sys, os, math
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst

inst, ah, T, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
I = read_inst(inst); vstart = I['vstart']
asg = int(ah, 16); fixed = (1 << vstart[T]) - 1; asg &= fixed
lines = []; nd = 0; ws = []
for c in I['cons']:
    m = c['m']; bad = set(c['bad'])
    s0 = 0; cols = []
    for q in range(m):
        f = c['forms'][q]
        if (bin(f & asg).count("1") & 1) ^ c["consts"][q]: s0 |= 1 << q
    # image of the free part: rows = forms restricted to free variables, as m x nfree matrix; image = span of columns
    frees = [c['forms'][q] & ~fixed for q in range(m)]
    # column space via transposition: build basis of the span of vectors v_j = (bit j of each row), j over free vars
    allf = 0
    for f in frees: allf |= f
    basis = {}
    j = allf
    while j:
        b = j & -j; jj = b.bit_length() - 1; j ^= b
        v = 0
        for q in range(m):
            if frees[q] >> jj & 1: v |= 1 << q
        for p in sorted(basis, reverse=True):
            if v >> p & 1: v ^= basis[p]
        if v: basis[v.bit_length() - 1] = v
    bv = list(basis.values()); r = len(bv)
    good = 0
    for mask in range(1 << r):
        x = s0
        for i in range(r):
            if mask >> i & 1: x ^= bv[i]
        if x not in bad: good += 1
    p = good / (1 << r)
    w = 99.0 if p == 0 else -math.log2(p)
    if r == 0: nd += 1; w = 0.0 if p > 0 else 99.0
    lines.append(f"{c['y']} {w:.6f}"); ws.append(w)
open(out, 'w').write('\n'.join(lines) + '\n')
print(f"condw: {len(lines)} words, {nd} fully determined, mean weight {sum(ws) / len(ws):.4f}, max {max(ws):.3f}")
