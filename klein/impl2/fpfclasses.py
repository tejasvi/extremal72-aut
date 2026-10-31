"""Enumerate Aut(Y) for the 41 codes, find conjugacy classes of fixed-point-free involutions."""
import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import is_aut

def compose(p, q):
    """(p*q)(i) = q(p(i)): first p then q."""
    return tuple(q[p[i]] for i in range(len(p)))

def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)

def closure(gens, n):
    e = tuple(range(n))
    G = {e}
    frontier = [e]
    while frontier:
        nf = []
        for g in frontier:
            for s in gens:
                h = compose(g, s)
                if h not in G:
                    G.add(h)
                    nf.append(h)
        frontier = nf
    return G

def fpf_involution_classes(G, gens, n):
    e = tuple(range(n))
    invs = [g for g in G if g != e and compose(g, g) == e and all(g[i] != i for i in range(n))]
    invset = set(invs)
    seen = set()
    classes = []
    for g in sorted(invs):
        if g in seen:
            continue
        orb = {g}
        fr = [g]
        while fr:
            nf = []
            for x in fr:
                for s in gens:
                    si = inverse(s)
                    y = compose(compose(si, x), s)
                    if y not in orb:
                        orb.add(y)
                        nf.append(y)
            fr = nf
        assert orb <= invset
        seen |= orb
        classes.append((g, len(orb)))
    return invs, classes

if __name__ == '__main__':
    codes = json.load(open(HERE + '/data/codes41.json'))
    auts = json.load(open(HERE + '/data/aut41.json'))
    out = []
    total = 0
    for c, a in zip(codes, auts):
        gens = [tuple(g) for g in a['gens']]
        G = closure(gens, 36)
        assert len(G) == int(float(a['grpsize'])), (len(G), a['grpsize'])
        invs, classes = fpf_involution_classes(G, gens, 36)
        ninv = sum(1 for g in G if g != tuple(range(36)) and compose(g, g) == tuple(range(36)))
        for (g, sz) in classes:
            assert is_aut(g, c['basis'], 36)
            # centralizer order = |G|/class size
        print(c['idx'], '|G|=', len(G), 'involutions', ninv, 'fpf', len(invs), 'fpf classes', len(classes),
              [sz for _, sz in classes], flush=True)
        total += len(classes)
        out.append(dict(idx=c['idx'], order=len(G), classes=[dict(beta=list(g), size=sz, centralizer=len(G) // sz) for g, sz in classes]))
    print('total instances', total)
    json.dump(out, open(HERE + '/data/fpf41.json', 'w'))
