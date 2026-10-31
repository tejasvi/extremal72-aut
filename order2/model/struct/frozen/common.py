"""Common helpers for c2explore: load the 41 self-dual [36,18,8] codes (Harada-Munemasa data via ~/c72/c2/codes36.txt),
span, weights.  Bit i of an int = coordinate i (same convention as ~/c72/c2par/autinv.py load())."""
import numpy as np
import os
CODES36 = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'codes36.txt')

def load():
    blocks = open(CODES36).read().strip().split('\n\n')
    codes = []
    for b in blocks:
        rows = [l.strip() for l in b.strip().split('\n') if l.strip()]
        codes.append([sum(int(ch) << j for j, ch in enumerate(r)) for r in rows])
    return codes

def span_np(gens):
    W = np.zeros(1, dtype=np.uint64)
    for g in gens:
        W = np.concatenate([W, W ^ np.uint64(g)])
    return W

def pc(x):
    return bin(x).count('1')

def rank(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)
