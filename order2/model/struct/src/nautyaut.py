"""Aut(Y) generators via dreadnaut for a binary code of length m: bipartite graph coordinates | words of the two
smallest weights; returns permutations of [m] that preserve the code (verified)."""
import subprocess
import numpy as np
from common import span_np, pc

def aut_gens(Ygens, m):
    W = span_np(Ygens); wt = np.bitwise_count(W)
    ws = sorted(set(int(x) for x in wt.tolist()) - {0})
    words = [int(x) for x in W[(wt == ws[0]) | (wt == ws[1])].tolist()]
    Wset = set(int(x) for x in W.tolist())
    nv = m + len(words)
    adj = [[] for _ in range(nv)]
    for k, w in enumerate(words):
        for i in range(m):
            if (w >> i) & 1: adj[i].append(m + k)
    lines = [f'n={nv} g']
    for i in range(m): lines.append(' '.join(map(str, adj[i])) + ';')
    for v in range(m, nv - 1): lines.append(';')
    lines.append('.')
    txt = '\n'.join(lines) + f'\nf=[0:{m-1}|{m}:{nv-1}]\nx\n'
    out = subprocess.run(['dreadnaut'], input=txt, capture_output=True, text=True).stdout
    gens = []; cur = None
    for line in out.split('\n'):
        s = line.strip()
        if line.startswith('('):
            if cur is not None: gens.append(cur)
            cur = s
        elif cur is not None and line.startswith(' ') and s and (s[0] == '(' or s[0].isdigit()):
            cur += ' ' + s
        else:
            if cur is not None: gens.append(cur); cur = None
    if cur is not None: gens.append(cur)
    perms = []
    for g in gens:
        p = list(range(nv))
        for cyc in g.replace(')', ')|').split('|'):
            cyc = cyc.strip()
            if not cyc: continue
            els = [int(x) for x in cyc.strip('()').split()]
            for a, b in zip(els, els[1:] + els[:1]): p[a] = b
        perms.append(p[:m])
    def ap(perm, w):
        o = 0
        for i in range(m):
            if (w >> i) & 1: o |= 1 << perm[i]
        return o
    perms = [p for p in perms if all(ap(p, g) in Wset for g in Ygens)]
    return perms
