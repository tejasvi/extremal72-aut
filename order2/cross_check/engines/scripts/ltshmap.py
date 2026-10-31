"""Compare the LTSH file of an augmented instance with the original package's sym.ltsh under the constraint index map
DER.map (new index of each original constraint).  Equal means: every table entry is identical, and every constraint
index in the augmented file is the mapped index of the original one (key line, c0, orbit lines c_u, per-g c_{g k_i}).
So the symmetry test reads exactly the original constraints' syndromes and never a derived constraint.  Audit code.
Usage: ltshmap.py ORIG_LTSH DER_LTSH DER_MAP"""
import sys


def parse(fn):
    tok = open(fn).read().split(); p = 0
    def take(n):
        nonlocal p
        v = tok[p:p + n]; p += n; return [int(x) for x in v]
    assert tok[0] == 'LTSH'; p = 1
    r, m0, c0, nO, nS0, nG, nCls = take(7)
    key = [take(2) for _ in range(r)]
    canon = take(1 << m0); hs0 = take(1 << m0)
    cls = []
    for _ in range(nCls):
        c, n = take(2); cls.append((c, take(n)))
    mul = take(nS0 * nS0)
    orb = []
    for _ in range(nO):
        cu = take(1)[0]; rows = take(m0); comp = take(nS0); orb.append((cu, rows, comp))
    gl = []
    if r > 1:
        for _ in range(nG):
            parts = []
            for i in range(1, r):
                c = take(1)[0]; parts.append((c, take(key[i][1])))
            gl.append(parts)
    assert p == len(tok)
    return dict(hdr=(r, m0, nO, nS0, nG, nCls), c0=c0, key=key, canon=canon, hs0=hs0, cls=cls, mul=mul, orb=orb, gl=gl)


def main():
    a, b = parse(sys.argv[1]), parse(sys.argv[2])
    omap = list(map(int, open(sys.argv[3]).read().split()))
    M = lambda c: omap[c]
    bad = []
    if a['hdr'] != b['hdr']: bad.append('header')
    if M(a['c0']) != b['c0']: bad.append('c0')
    if [(M(c), m) for c, m in a['key']] != [tuple(x) for x in b['key']]: bad.append('key line')
    for k in ('canon', 'hs0', 'cls', 'mul'):
        if a[k] != b[k]: bad.append(k)
    if [(M(cu), rows, comp) for cu, rows, comp in a['orb']] != b['orb']: bad.append('orbit lines')
    if [[(M(c), rows) for c, rows in parts] for parts in a['gl']] != b['gl']: bad.append('g lines')
    used = {b['c0']} | {c for c, m in b['key']} | {cu for cu, _, _ in b['orb']} | {c for parts in b['gl'] for c, _ in parts}
    if not used <= set(omap): bad.append('refers to a non-original (derived) constraint')
    print('RESULT', 'PASS' if not bad else 'FAIL ' + ', '.join(bad), sys.argv[2], f'(constraint indices referenced: {len(used)}, all original)' if not bad else '')


if __name__ == '__main__':
    main()
