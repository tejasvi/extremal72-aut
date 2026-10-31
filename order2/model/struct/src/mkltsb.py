"""Bit-granular LTS data (file 'LTSB') for src/lwe10b.c.  For every g in G = Aut(Y) and every bit j of the key
word's syndrome: the transported bit s_k0(B^g)_j = B(g k0, g ub0_j) is the parity of a fixed combination of the
syndrome forms of the constraint holding u = g k0, i.e. one linear form F_{g,j} over the variables plus a constant.
Its level is the level of its highest variable (-1 if F = 0).  lwe10b uses it to compare a comparand bit by bit,
MSB first, before the whole transported syndrome is determined.
File: 'LTSB nG m0 c0', then per g one line 'lv(c_u) F_0 c_0 L_0 ... F_{m0-1} c_{m0-1} L_{m0-1}' (F in hex).
Usage: mkltsb.py CI INSTANCE LTSHFILE OUT"""
import sys, os, pickle
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst
from partbits_lib import closure, ap
from rebasis import coords

ci, inst, ltsh, out = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
I = read_inst(inst); cons = I['cons']; vstart = I['vstart']
idx = {c['y']: k for k, c in enumerate(cons)}
hdr = open(ltsh).readline().split(); c0 = int(hdr[3]); m0 = int(hdr[2])
k0 = cons[c0]['y']; ub0 = cons[c0]['ub']; assert len(ub0) == m0
perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
G = closure([tuple(p) for p in perms])
assert len(G) == int(hdr[6]), "group order differs from the LTSH header"


def level_of(F):
    if F == 0: return -1
    b = F.bit_length() - 1
    for t in range(len(vstart) - 1):
        if vstart[t] <= b < vstart[t + 1]: return t
    raise ValueError


lines = []
for g in G:
    u = ap(g, k0); cu = idx[u]; X = cons[cu]
    parts = [str(X['lv'])]
    for j in range(m0):
        R = coords(X['ub'], ap(g, ub0[j]))
        F = 0; c = 0
        for i in range(X['m']):
            if R >> i & 1: F ^= X['forms'][i]; c ^= X['consts'][i]
        parts += [f'{F:x}', str(c), str(level_of(F))]
    lines.append(' '.join(parts))
with open(out, 'w') as f:
    f.write(f'LTSB {len(G)} {m0} {c0}\n' + '\n'.join(lines) + '\n')
print(f"LTSB: |G|={len(G)} m0={m0} k0={k0} (constraint {c0}, level {cons[c0]['lv']})")
