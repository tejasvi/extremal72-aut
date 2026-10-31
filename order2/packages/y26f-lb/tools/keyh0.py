"""Key stabiliser H0 = {g in G : g fixes every key word and acts trivially on its syndrome coordinates}.
LTS cannot separate B from B^g for g in H0 (K(B^g) = K(B) for all B), so |H0| > 1 costs a factor |H0|.
Usage: keyh0.py CI INSTANCE WORDS(comma)"""
import sys, os, pickle
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from symprep import closure, ap, coords_fn
def key_h0(perms, inst, key, G=None):
    G = G or closure(perms, 36)
    ub = {}
    for l in open(inst + '.meta'):
        row = list(map(int, l.split())); ub[row[0]] = row[1:]
    n = 0
    cos = {k: coords_fn(ub[k]) for k in key}
    for g in G:
        ok = True
        for k in key:
            if ap(g, k, 36) != k: ok = False; break
            u = ub[k]; co = cos[k]
            if any(co(ap(g, u[j], 36)) != (1 << j) for j in range(len(u))): ok = False; break
        n += ok
    return n
if __name__ == '__main__':
    ci = int(sys.argv[1]); perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
    key = [int(x) for x in sys.argv[3].split(',')]
    print("|H0| =", key_h0(perms, sys.argv[2], key))
