"""Rewrite one constraint of an instance in a new syndrome basis (same span Y_y): new basis words ub'_i =
sum_j T_ij ub_j, forms'_i = sum_j T_ij forms_j, consts'_i = sum_j T_ij consts_j, bad' = {T s}.  The constraint is
unchanged as a set condition, so raw node counts are identical; only the integer reading of its syndrome (and so
the LTS lex order when it is a key word) changes.
Usage: rebasis.py INST_IN INST_OUT WORD NEWBASIS(comma-separated words, MSB last as in the instance)"""
import sys, os
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst, write_inst


def coords(basis, x):
    """coordinates of x in basis (list of ints) over F2; raises if x is not in the span."""
    piv = []          # (pivot bit, vector, combination mask)
    for j, b in enumerate(basis):
        v, c = b, 1 << j
        for pb, pv, pc in piv:
            if v >> pb & 1: v ^= pv; c ^= pc
        assert v, "basis not independent"
        piv.append((v.bit_length() - 1, v, c))
    v, c = x, 0
    for pb, pv, pc in piv:
        if v >> pb & 1: v ^= pv; c ^= pc
    assert v == 0, "word not in span"
    return c


def parity(x):
    return bin(x).count('1') & 1


if __name__ == '__main__':
    fin, fout, w = sys.argv[1], sys.argv[2], int(sys.argv[3]); nb = [int(x) for x in sys.argv[4].split(',')]
    I = read_inst(fin); cons = I['cons']
    k = [i for i, c in enumerate(cons) if c['y'] == w]; assert len(k) == 1; c = cons[k[0]]
    m = c['m']; assert len(nb) == m
    T = [coords(c['ub'], x) for x in nb]                       # row i: coordinates of ub'_i in the old basis
    forms = []; consts = []
    for i in range(m):
        f = 0; k_ = 0
        for j in range(m):
            if T[i] >> j & 1: f ^= c['forms'][j]; k_ ^= c['consts'][j]
        forms.append(f); consts.append(k_)
    bad = sorted(sum(parity(T[i] & s) << i for i in range(m)) for s in c['bad'])
    assert len(set(bad)) == len(c['bad'])
    c['forms'], c['consts'], c['bad'], c['ub'] = forms, consts, bad, nb
    write_inst(fout, I['N'], I['vstart'], cons)
    print(f"rewrote constraint {k[0]} (word {w}, m={m}) in the new basis; {len(bad)} bad syndromes")
