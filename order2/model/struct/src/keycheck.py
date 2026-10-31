"""Checkability-based LTS key selection.  For an instance (with .meta) and Aut(Y) generators: every G-orbit O of
low words, the level at which ALL words of O are checkable (max constraint level + 1; free riders included), and
a crude estimate of the LTS tree when the key's first word is taken from O:
  factor_t = |G|                        if all of O is checkable at level t,
           = |S0| * #(O checkable at t)   otherwise (prenecklace-type partial comparison; 1 if none),
  est = sum_t raw_t / factor_t,   raw_t from a RAWPROF probe line (per-level raw node estimates).
Compares with the same estimate for the orbit of the current key's first word.
Usage: keycheck.py CI INSTANCE [RAWPROF_FILE|-] [CURRENT_KEY_WORD]"""
import sys, os, pickle, re
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst


def closure_size(perms):
    idp = tuple(range(36)); seen = {idp}; fr = [idp]
    while fr:
        nf = []
        for p in fr:
            for g in perms:
                q = tuple(g[p[i]] for i in range(36))
                if q not in seen:
                    seen.add(q); nf.append(q)
        fr = nf
    return len(seen)


def ap(p, y):
    z = 0
    while y:
        b = y & -y; i = b.bit_length() - 1; z |= 1 << p[i]; y ^= b
    return z


def orbits(cons, perms):
    lev = {c['y']: c['lv'] for c in cons}; wt = {c['y']: c['wt'] for c in cons}
    seen = set(); out = []
    for c in cons:
        y = c['y']
        if y in seen: continue
        orb = {y}; st = [y]
        while st:
            x = st.pop()
            for p in perms:
                z = ap(p, x)
                if z not in orb: orb.add(z); st.append(z)
        seen |= orb
        out.append(dict(words=sorted(orb, key=lambda x: (lev[x], x)), wt=wt[y], levels=sorted(lev[x] for x in orb)))
    return out


SHIFT = int(os.environ.get('KCSHIFT', '1'))   # 1 (corrected, 2026-10-21 ~21:30 UTC): nodes counted at level t are reduced only
# by words whose constraint level is <= t-2 (the engine counts a node before its own level-t tests); 0 = the old convention
def estimate(o, nG, raw, NLEV):
    n = len(o['words']); s0 = nG // n
    est = 0.0; prof = []
    for t in range(NLEV + 1):
        d = sum(1 for l in o['levels'] if l < t - SHIFT)
        f = nG if d == n else (s0 * d if d > 0 else 1)
        if raw is not None and t < len(raw): est += raw[t] / f
        prof.append(f)
    return est, prof


def read_raw(fn):
    for l in open(fn):
        if 'RAWPROF' in l or ('PROBE estimate' in l and 'LTS' not in l):
            vals = re.findall(r' (\d+):([\d.e+-]+)', l)
            return [float(v) for k, v in vals]
    return None


if __name__ == '__main__':
    ci = int(sys.argv[1]); I = read_inst(sys.argv[2]); cons = I['cons']
    raw = read_raw(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
    cur = int(sys.argv[4]) if len(sys.argv) > 4 else None
    perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
    nG = closure_size(perms)
    obs = orbits(cons, perms)
    res = []
    for o in obs:
        e, prof = estimate(o, nG, raw, I['NLEV'])
        res.append((e, max(o['levels']) + 1, len(o['words']), o['wt'], o, prof))
    res.sort(key=lambda r: (r[0], r[1]))
    rawtot = sum(raw) if raw else 0
    print(f"Y{ci} |G|={nG} orbits={len(obs)} raw total {rawtot:.3e} raw/|G| {rawtot / nG:.3e}")
    if raw: print("raw profile:", ' '.join(f"{x:.2g}" for x in raw))
    for e, comp, n, w, o, prof in res[:6]:
        print(f"  est {e:.3e} complete-at {comp:2d} |O|={n:4d} wt {w:2d} levels {o['levels'][:20]}{'...' if n > 20 else ''}")
    print("BESTWORDS " + ','.join(map(str, res[0][4]['words'])))
    for i, r in enumerate(res[:int(os.environ.get('KCTOP', '0'))]):
        print(f"ORBITWORDS {i} est {r[0]:.3e} n {r[2]} wt {r[3]} " + ','.join(map(str, r[4]['words'])))
    if cur is not None:
        for e, comp, n, w, o, prof in res:
            if cur in o['words']:
                print(f"  CURRENT key orbit: est {e:.3e} complete-at {comp} |O|={n} wt {w}")
