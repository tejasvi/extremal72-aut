"""Automorphism groups of binary codes via nauty's dreadnaut (bipartite incidence graph
coordinates <-> low-weight codewords, weights added until the words span the code)."""
import sys, subprocess, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
import numpy as np

def low_weight_words_spanning(basis, n):
    """Smallest w such that words of weight <= w span the code; return (w, words)."""
    arr = span_array(basis)
    wts = popcount_array(arr)
    k = len(basis)
    for w in range(1, n + 1):
        words = [int(x) for x in arr[(wts > 0) & (wts <= w)]]
        if words and rank(words) == k:
            return w, words
    raise RuntimeError

def dreadnaut_aut(n, words):
    """Aut group of the set system 'words' on n points (as permutations of range(n)).
    Returns (generators as tuples p with p[i] = image of i, grpsize string)."""
    N = n + len(words)
    lines = ["n=%d g" % N]
    adj = [[] for _ in range(N)]
    for j, w in enumerate(words):
        v = n + j
        for i in range(n):
            if (w >> i) & 1:
                adj[i].append(v)
    for i in range(N):
        lines.append(" ".join(str(x) for x in adj[i]) + ";")
    lines[-1] = lines[-1][:-1] + "."
    lines.append("f=[0:%d|%d:%d]" % (n - 1, n, N - 1))
    lines.append("x")
    inp = "\n".join(lines) + "\n"
    out = subprocess.run(["dreadnaut"], input=inp, capture_output=True, text=True).stdout
    gens = []
    cur = None
    for line in out.splitlines():
        s = line.strip()
        if line.startswith("("):
            if cur is not None:
                gens.append(cur)
            cur = s
        elif cur is not None and line[:1].isspace() and s:
            cur += " " + s
        else:
            if cur is not None:
                gens.append(cur)
                cur = None
    if cur is not None:
        gens.append(cur)
    m = re.search(r"grpsize=([0-9.e]+)", out)
    grpsize = m.group(1)
    perms = []
    for g in gens:
        p = list(range(N))
        for cyc in re.findall(r"\(([^)]*)\)", g):
            pts = [int(t) for t in cyc.split()]
            for a, b in zip(pts, pts[1:] + pts[:1]):
                p[a] = b
        # restrict to coordinates
        assert all(p[i] < n for i in range(n))
        perms.append(tuple(p[:n]))
    return perms, grpsize, out

def apply_perm_vec(p, v):
    """Coordinate i of v moves to position p[i]."""
    w = 0
    i = 0
    while v:
        if v & 1:
            w |= 1 << p[i]
        v >>= 1
        i += 1
    return w

def is_aut(p, basis, n):
    S = Span(basis)
    return all(S.contains(apply_perm_vec(p, b)) for b in basis)
