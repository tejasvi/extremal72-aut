"""Shared helpers for partbits.py / partsim.py: group closure and fast permutation action on 36-bit words."""


def closure(perms):
    idp = tuple(range(36)); seen = {idp}; fr = [idp]
    while fr:
        nf = []
        for p in fr:
            for g in perms:
                q = tuple(g[p[i]] for i in range(36))
                if q not in seen: seen.add(q); nf.append(q)
        fr = nf
    return sorted(seen)


_tab = {}


def ap(p, y):
    t = _tab.get(p)
    if t is None:
        t = []
        for k in range(5):
            row = []
            for b in range(256):
                z = 0
                for i in range(8):
                    if b >> i & 1 and 8 * k + i < 36: z |= 1 << p[8 * k + i]
                row.append(z)
            t.append(row)
        _tab[p] = t
    return t[0][y & 255] | t[1][y >> 8 & 255] | t[2][y >> 16 & 255] | t[3][y >> 24 & 255] | t[4][y >> 32 & 255]
