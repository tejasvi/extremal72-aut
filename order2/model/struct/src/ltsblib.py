"""Generic LTSB writer (see mkltsb.py) for words of any length m: make_ltsb(H, m, inst, ltsh, out), H = list of
permutation tuples of range(m) (the group of the LTSH file, same order), inst = instance with .meta."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst
from rebasis import coords


def apm(p, y):
    z = 0
    while y:
        b = y & -y; i = b.bit_length() - 1; z |= 1 << p[i]; y ^= b
    return z


def make_ltsb(H, m, inst, ltsh, out):
    I = read_inst(inst); cons = I['cons']; vstart = I['vstart']
    idx = {c['y']: k for k, c in enumerate(cons)}
    hdr = open(ltsh).readline().split(); c0 = int(hdr[3]); m0 = int(hdr[2])
    assert int(hdr[6]) == len(H)
    k0 = cons[c0]['y']; ub0 = cons[c0]['ub']
    def level_of(F):
        if F == 0: return -1
        b = F.bit_length() - 1
        for t in range(len(vstart) - 1):
            if vstart[t] <= b < vstart[t + 1]: return t
        raise ValueError
    lines = []
    for g in H:
        u = apm(g, k0); X = cons[idx[u]]; parts = [str(X['lv'])]
        for j in range(m0):
            R = coords(X['ub'], apm(g, ub0[j])); F = 0; c = 0
            for i in range(X['m']):
                if R >> i & 1: F ^= X['forms'][i]; c ^= X['consts'][i]
            parts += [f'{F:x}', str(c), str(level_of(F))]
        lines.append(' '.join(parts))
    with open(out, 'w') as f: f.write(f'LTSB {len(H)} {m0} {c0}\n' + '\n'.join(lines) + '\n')
    return k0, c0
