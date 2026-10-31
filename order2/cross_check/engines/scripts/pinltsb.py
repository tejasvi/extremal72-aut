"""Transform a bit-granular LTS file (sym.ltsb) for a sub-instance made by pin.py (variables of levels < L pinned to the
prefix X0 and the rest renumbered): every bit form F becomes F >> P with constant c ^ parity(F & X0), P = vstart[L], and
its level becomes the level of the new form in the sub-instance (-1 for a form of pinned variables only).  On
assignments that extend X0 every bit keeps its value, and the comparands keep their constraints and order, so at levels
>= L the bit test of the sub-instance is the original test restricted to the subtree below X0.  On the pinned path
(levels < L, one node each) the bits of pinned variables count as determined from the start (audit code).
Usage: pinltsb.py INSTANCE LTSB L PREFIXHEX OUT"""
import sys


def par(x): return x.bit_count() & 1


def main():
    inst, ltsb, L, x0, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4], 16), sys.argv[5]
    with open(inst) as f:
        N, NLEV, NC = map(int, f.readline().split()); vs = list(map(int, f.readline().split()))
    P = vs[L]; x0 &= (1 << P) - 1
    vs2 = [max(0, v - P) for v in vs]

    def lvl(v):                                   # as the engines' lb_lvl, on the sub-instance's vstart
        if v == 0: return -1
        hb = v.bit_length() - 1
        for t in range(NLEV):
            if vs2[t] <= hb < vs2[t + 1]: return t
        raise SystemExit('form beyond the variables')
    tok = open(ltsb).read().split()
    assert tok[0] == 'LTSB'; nG, m0, c0 = int(tok[1]), int(tok[2]), int(tok[3]); i = 4
    o = [f'LTSB {nG} {m0} {c0}']
    for g in range(nG):
        lu = int(tok[i]); i += 1; row = [str(lu)]
        for j in range(m0):
            F, c, l = int(tok[i], 16), int(tok[i + 1]), int(tok[i + 2]); i += 3
            F2, c2 = F >> P, c ^ par(F & x0)
            l2 = lvl(F2)
            assert l2 == -1 or l2 == l, (g, j, l, l2)  # a form with a free variable keeps its level
            row += [f'{F2:x}', str(c2), str(l2)]
        o.append(' '.join(row))
    assert i == len(tok)
    open(out, 'w').write('\n'.join(o) + '\n')


if __name__ == '__main__':
    main()
