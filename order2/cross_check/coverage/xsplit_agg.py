"""Split cross-check rule (audit's own implementation, for fleet's XSPLIT proposal): N sub-part logs of the reference
engine, run as (SPL, N*NPART, p + j*NPART), against the log of part p of NPART.
usage: xsplit_agg.py [--no-leaf] [--banner TEXT] PROD_LOG NPART SUB_LOG...      (cov_c2.py imports problems())
Levels < SPL: every LEVEL line equal. Level SPL: kt, ncons, nodes and the three prunes equal, kids summed. Levels > SPL:
kt, ncons equal, counters summed. Leaf line (SYMPRUNE/LTSPRUNE/LHPRUNE at leaves, level NLEV > SPL) summed. LBPRUNE
t <= SPL equal, t > SPL summed, present in all logs or in none. SOLUTION lines: multiset union; nsol summed. Every log:
one DONE line, no STOPPED and no other line type, the same levels, split SPL and N equal to the production log's; the
sub-parts' modulus is N*NPART for the number N of logs, and their parts are p + j*NPART for j = 0..N-1, each exactly
once. --no-leaf drops the leaf line (the rule as first proposed), to show what it misses."""
import re, sys
from collections import Counter

def parse(fn, banner=None):
    """banner: the exact text of the package's rc14g stderr banner, skipped where it is a whole line (only the production
    log is read with it; cov_c2.py allows it only in parts that ENGINES.txt lists as rc14g). Sub-part logs of the
    reference engine are read without it, so a banner there fails"""
    L = {}; d = None; leaf = None; lb = None; sol = Counter(); stopped = 0; ndone = 0; other = 0
    for ln in open(fn, errors='replace'):
        w = ln.split()
        if not w: continue
        if banner is not None and ln.rstrip('\n') == banner: continue
        if w[0] not in ('LEVEL', 'DONE', 'SYMPRUNE', 'LBPRUNE', 'SOLUTION', 'STOPPED'): other += 1
        elif w[0] == 'LEVEL': L[int(w[1])] = {w[i]: int(w[i + 1]) for i in range(2, len(w) - 1, 2)}
        elif w[0] == 'DONE':
            ndone += 1
            m = re.search(r'nsol (\d+) time \d+s split (-?\d+) part (\d+)/(\d+) N (\d+)', ln)
            d = tuple(int(x) for x in m.groups()) if m else None
        elif w[0] == 'SYMPRUNE' and 'leaves' in ln: leaf = tuple(int(x) for x in re.findall(r'leaves (\d+)', ln))
        elif w[0] == 'LBPRUNE': lb = {int(x.split(':')[0]): int(x.split(':')[1]) for x in w[1:]}
        elif w[0] == 'SOLUTION': sol[w[1]] += 1
        elif w[0] == 'STOPPED': stopped += 1
    return dict(L=L, d=d, leaf=leaf, lb=lb, sol=sol, stopped=stopped, ndone=ndone, other=other)

def problems(prod, npart, subs, leaf=True, banner=None):
    """[] if the sub-part logs subs add up to the production log prod of part p of npart, else the differences"""
    P = parse(prod, banner=banner); S = [parse(f) for f in subs]; bad = []
    for fn, x in [(prod, P)] + list(zip(subs, S)):
        if x['stopped'] or x['ndone'] != 1 or not x['d'] or x['other']:
            bad.append(f'{fn}: STOPPED {x["stopped"]}, DONE lines {x["ndone"]}, lines of another type {x["other"]}')
    if bad or not S: return bad or ['no sub-part logs']
    nsol, spl, part, npp, nv = P['d']
    if npp != npart: bad.append(f'production modulus {npp} != {npart}')
    n = len(S)
    if sorted(x['d'][2] for x in S) != [part + j * npart for j in range(n)]: bad.append('sub-part ids are not p + j*NPART, j = 0..N-1, each once')
    for fn, x in zip(subs, S):
        if x['d'][1] != spl or x['d'][3] != n * npart or x['d'][4] != nv: bad.append(f'{fn}: split/modulus/N {x["d"][1:]} != {spl}/{n * npart}/{nv}')
        if set(x['L']) != set(P['L']): bad.append(f'{fn}: LEVEL lines for levels {sorted(set(x["L"]) ^ set(P["L"]))} in one log only')
    if sum(x['d'][0] for x in S) != nsol: bad.append('nsol does not sum')
    if sum((x['sol'] for x in S), Counter()) != P['sol']: bad.append('SOLUTION multisets differ')
    for t in sorted(P['L']):
        pl = P['L'][t]
        for fn, x in zip(subs, S):
            if t not in x['L']: continue
            sl = x['L'][t]
            eq = list(pl) if t < spl else (['kt', 'ncons', 'nodes', 'symprune', 'ltsprune', 'lhprune'] if t == spl else ['kt', 'ncons'])
            for k in eq:
                if sl.get(k) != pl[k]: bad.append(f'{fn}: LEVEL {t} {k} {sl.get(k)} != {pl[k]}')
        summed = [] if t < spl else (['kids'] if t == spl else ['nodes', 'kids', 'symprune', 'ltsprune', 'lhprune'])
        for k in summed:
            s = sum(x['L'].get(t, {}).get(k, 0) for x in S)
            if s != pl[k]: bad.append(f'LEVEL {t} {k}: sum {s} != {pl[k]}')
    if leaf:
        if P['leaf'] is None or any(x['leaf'] is None for x in S): bad.append('leaf line missing')
        elif tuple(map(sum, zip(*[x['leaf'] for x in S]))) != P['leaf']: bad.append(f'leaf counters do not sum: {[x["leaf"] for x in S]} vs {P["leaf"]}')
    if len(set(x['lb'] is None for x in [P] + S)) > 1:
        bad.append('LBPRUNE line present in some logs only')
    elif P['lb'] is not None:
        if any(set(x['lb']) != set(P['lb']) for x in S): bad.append('LBPRUNE levels differ')
        for t, v in P['lb'].items():
            vals = [x['lb'].get(t) for x in S]
            if (t <= spl and any(v2 != v for v2 in vals)) or (t > spl and sum(v2 or 0 for v2 in vals) != v): bad.append(f'LBPRUNE {t}: {vals} vs {v}')
    return bad

if __name__ == '__main__':
    args = sys.argv[1:]
    noleaf = '--no-leaf' in args
    args = [a for a in args if a != '--no-leaf']
    banner = None
    if args and args[0] == '--banner': banner, args = args[1], args[2:]   # exact banner text of the production engine
    bad = problems(args[0], int(args[1]), args[2:], leaf=not noleaf, banner=banner)
    print('IDENTICAL' if not bad else 'DIFFER: ' + '; '.join(bad[:6]))
