"""Write an LTSH symmetry file for an instance with a chosen key (frozen symprep3.prep3).
Usage: mkkey.py CI INSTANCE FLAGFILE OUT KEYSPEC
KEYSPEC: 'flag:R' (first R flag vectors) | 'words:w1,w2,...' | 'orbit:LEVMAX:R' (R words of the lowest-level
G-orbit whose words all have constraint level <= LEVMAX, sorted by level, ties by word value)."""
import sys, os, pickle
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from symprep3 import prep3
from instio import read_inst
ci = int(sys.argv[1]); inst = sys.argv[2]; flagf = sys.argv[3]; out = sys.argv[4]; spec = sys.argv[5]
flag = [int(x) for x in [l for l in open(flagf) if l.startswith('FLAG')][0].split()[1:]]
perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
if spec.startswith('flag:'):
    key = flag[:int(spec[5:])]
elif spec.startswith('early:'):
    # component 0: a word of the orbit that is complete earliest (ties: smaller orbit, then earlier word); then the
    # earliest-checkable words by constraint level (weight 8 first), up to R words; H0 fix applied below
    R = int(spec.split(':')[1])
    from keycheck import orbits as _orbs
    I = read_inst(inst); lev = {c['y']: c['lv'] for c in I['cons']}; wt = {c['y']: c['wt'] for c in I['cons']}
    obs = _orbs(I['cons'], perms)
    o0 = min(obs, key=lambda o: (max(o['levels']), len(o['words']), min(o['levels'])))
    k0 = min(o0['words'], key=lambda x: (lev[x], x))
    rest = sorted((c['y'] for c in I['cons'] if c['y'] != k0), key=lambda x: (lev[x], -(wt[x] == 8), x))
    key = [k0] + rest[:R - 1]
    print(f"early key: k0 orbit size {len(o0['words'])} complete at {max(o0['levels']) + 1}; levels {[lev[x] for x in key]}")
    spec = 'h0fix:' + ','.join(map(str, key))
elif spec.startswith('h0fix:'):
    key = [int(x) for x in spec[6:].split(',')]
elif spec.startswith('words:'):
    key = [int(x) for x in spec[6:].split(',')]
elif spec.startswith('orbit:'):
    _, lm, R = spec.split(':'); lm = int(lm); R = int(R)
    I = read_inst(inst); lev = {c['y']: c['lv'] for c in I['cons']}
    def ap(p, y):
        z = 0
        while y:
            b = y & -y; i = b.bit_length() - 1; z |= 1 << p[i]; y ^= b
        return z
    seen = set(); best = None
    for c in sorted(I['cons'], key=lambda c: c['lv']):
        y = c['y']
        if y in seen: continue
        orb = {y}; st = [y]
        while st:
            x = st.pop()
            for p in perms:
                z = ap(p, x)
                if z not in orb: orb.add(z); st.append(z)
        seen |= orb
        if max(lev[x] for x in orb) <= lm and len(orb) >= R:
            cand = sorted(orb, key=lambda x: (lev[x], x))
            if best is None or len(orb) > len(best): best = cand
    assert best, "no orbit"
    key = best[:R]
    print("orbit size", len(best), "key levels", [lev[x] for x in key])
elif spec.startswith('auto:'):
    # checkability-based key: orbits sorted by (completion level, -bits per word, -size); take words orbit by orbit
    # (each orbit's words sorted by level) until total syndrome bits >= log2|G| + MARGIN or RMAX words
    import math
    from keycheck import orbits as orbs_of, closure_size
    _, margin, rmax = spec.split(':'); margin = float(margin); rmax = int(rmax)
    I = read_inst(inst); nG = closure_size(perms)
    bits = {8: 10, 10: 8, 12: 6}
    obs = orbs_of(I['cons'], perms)
    obs.sort(key=lambda o: (max(o['levels']), -bits[o['wt']], -len(o['words'])))
    key = []; tb = 0; lastlev = None
    for o in obs:
        for x in o['words']:
            if len(key) >= rmax or tb >= math.log2(nG) + margin: break
            key.append(x); tb += bits[o['wt']]; lastlev = max(o['levels']) + 1
        if len(key) >= rmax or tb >= math.log2(nG) + margin: break
    print(f"auto key: |G|={nG} words {len(key)} bits {tb} all orbits complete at level {lastlev}")
else:
    raise SystemExit("bad keyspec")
from keyh0 import key_h0 as _kh0
from symprep import closure as _clos
_G = _clos(perms, 36)
def key_h0(key): return _kh0(perms, inst, key, _G)
if spec.startswith('auto:') or spec.startswith('h0fix:'):
    if spec.startswith('h0fix:'):
        key = [int(x) for x in spec.split(':', 1)[1].split(',')]
    I2 = read_inst(inst); lev2 = {c['y']: c['lv'] for c in I2['cons']}
    from keycheck import orbits as orbs_of2
    obs2 = sorted(orbs_of2(I2['cons'], perms), key=lambda o: (max(o['levels']), -len(o['words'])))
    cands = [x for o in obs2 for x in o['words'] if x not in key]
    h = key_h0(key)
    while h > 1 and len(key) < 16:
        best = None
        for x in cands[:200]:
            hx = key_h0(key + [x])
            sc = (hx, max(lev2[x], 0))
            if best is None or sc < best[0]: best = (sc, x)
        key.append(best[1]); cands.remove(best[1]); h = best[0][0]
        print(f"  h0fix: added word at level {lev2[best[1]]} -> |H0| = {h}")
    print(f"key stabiliser |H0| = {h}; key levels {[lev2[x] for x in key]}")
prep3(perms, 36, inst, out, flag, len(key), key=key)
print("KEY", ' '.join(map(str, key)))
