"""Automorphism group of a self-dual code via nauty on the coordinate/low-weight-word incidence graph."""
import sys
sys.path.insert(0, "<HOME>/c72_indep/y18/src")
from codes import *
import pynauty


def low_weight_spanning_set(G, n):
    words = span(G)
    wd = weight_distribution(words, n)
    d = min(i for i in range(1, n + 1) if wd[i])
    for w in range(d, n + 1, 2):
        S = [v for v in words if 0 < wt(v) <= w]
        if rank(S, n) == len(G):
            return S, w
    raise RuntimeError


def aut_group(S, n):
    """Return (order, generators as lists perm[i] on coordinates) of Aut of the set system S on [n]."""
    N = n + len(S)
    adj = {i: [] for i in range(N)}
    for j, v in enumerate(S):
        for i in range(n):
            if v >> i & 1:
                adj[i].append(n + j)
    g = pynauty.Graph(N, directed=False, adjacency_dict=adj,
                      vertex_coloring=[set(range(n)), set(range(n, N))])
    gens, grpsize1, grpsize2, orbits, numorb = pynauty.autgrp(g)
    order = round(grpsize1 * 10 ** grpsize2)
    return order, [list(p[:n]) for p in gens]


def apply_perm(v, p, n):
    """(gv)_{p[i]} = v_i."""
    out = 0
    for i in range(n):
        if v >> i & 1:
            out |= 1 << p[i]
    return out


if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 39
    G = read_code36(k)
    n = 36
    S, w = low_weight_spanning_set(G, n)
    print("words of weight <=", w, "span the code; count", len(S))
    order, gens = aut_group(S, n)
    print("|Aut| =", order, "generators:", len(gens))
    words = set(span(G))
    for p in gens:
        for b in G:
            assert apply_perm(b, p, n) in words
    print("generators preserve the code: ok")
