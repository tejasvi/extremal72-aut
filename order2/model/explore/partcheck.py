"""Structural check of every part log of a split run, including bit-granular LTS (rc11, LTSBFILE) packages.
Per part: exactly one DONE line for this part/NPART/split, NLEV LEVEL lines 0..NLEV-1, one 'SYMPRUNE at leaves' line,
no STOPPED, SOLUTION lines counted, unknown lines reported; with LTSBFILE in PLAN.txt exactly one LBPRUNE line with
entries 0..NLEV and lbprune[t] <= lhprune[t] (lhprune at leaves for t = NLEV); without it no LBPRUNE line.
Across parts: the prefix signature (LEVEL lines of levels < SPL, the level-SPL line without its kids field, and the
LBPRUNE entries of levels <= SPL) must be identical, since every part recounts the prefix; a part from another package
variant (with or without LTSB, other inputs) would differ there or in its LBPRUNE line.
Usage: partcheck.py PKGDIR PARTSDIR NPART SPL [PARTLIST]   (PARTLIST: comma-separated subset, for tests)"""
import collections, os, re, sys

pkgdir, d, npart, spl = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
plan = open(f'{pkgdir}/PLAN.txt').read()
m = re.search(r'^LTSBFILE (\S+)', plan, re.M)
lb = m.group(1) if m else None
rL = re.compile(r'^LEVEL (\d+) kt (\d+) ncons (\d+) nodes (\d+) kids (\d+) symprune (\d+) ltsprune (\d+) lhprune (\d+)$')
rD = re.compile(r'^DONE lwe nsol (\d+) time \d+s split (-?\d+) part (\d+)/(\d+) N (\d+)$')
rS = re.compile(r'^SYMPRUNE at leaves (\d+) LTSPRUNE at leaves (\d+) LHPRUNE at leaves (\d+)$')
rB = re.compile(r'^LBPRUNE((?: \d+:\d+)+)$')
rG = re.compile(r'^lwe11: generated lane loops for levels( \d+)+$')
ngen = 0
probs = collections.defaultdict(list); sigs = collections.Counter(); sig_of = {}; nlev0 = None
lbsum = collections.Counter(); lbpre = None; nsol = 0; unknown = collections.Counter(); nlb = 0
for p in ([int(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else range(npart)):
    fn = os.path.join(d, f'p{p}.log')
    if not os.path.exists(fn): probs['missing'].append(p); continue
    lev = {}; done = []; sym = []; lbl = []
    for line in open(fn).read().splitlines():
        if (x := rL.match(line)): lev.setdefault(int(x.group(1)), []).append(tuple(int(v) for v in x.groups()))
        elif (x := rD.match(line)): done.append(x.groups())
        elif (x := rS.match(line)): sym.append(tuple(int(v) for v in x.groups()))
        elif (x := rB.match(line)): lbl.append(x.group(1))
        elif line.startswith('SOLUTION'): nsol += 1
        elif line.startswith('STOPPED'): probs['STOPPED'].append(p)
        elif rG.match(line): ngen += 1   # rc14g's informational line about its generated loops (no counts, not compared)
        else: unknown[line.split(' ')[0][:20]] += 1; probs['unknown line'].append(p)
    if len(done) != 1 or int(done[0][2]) != p or int(done[0][3]) != npart or int(done[0][1]) != spl:
        probs['DONE line'].append(p); continue
    nsol += int(done[0][0])
    nlev = len(lev)
    if nlev0 is None: nlev0 = nlev
    if sorted(lev) != list(range(nlev0)) or any(len(v) != 1 for v in lev.values()): probs['LEVEL lines'].append(p); continue
    if len(sym) != 1: probs['SYMPRUNE line'].append(p); continue
    L = {t: v[0] for t, v in lev.items()}
    lbv = None
    if lb:
        if len(lbl) != 1: probs['LBPRUNE line count'].append(p); continue
        e = dict((int(a), int(b)) for a, b in (x.split(':') for x in lbl[0].split()))
        if sorted(e) != list(range(nlev0 + 1)): probs['LBPRUNE entries'].append(p); continue
        lhp = [L[t][7] for t in range(nlev0)] + [sym[0][2]]
        if any(e[t] > lhp[t] for t in range(nlev0 + 1)): probs['lbprune > lhprune'].append(p)
        lbv = e; nlb += 1
        for t in range(spl + 1, nlev0 + 1): lbsum[t] += e[t]
    elif lbl: probs['LBPRUNE line in a package without LTSBFILE'].append(p)
    sig = tuple(L[t] for t in range(spl)) + (L[spl][:4] + L[spl][5:],) + (tuple(lbv[t] for t in range(spl + 1)) if lbv else ())
    sigs[sig] += 1; sig_of[p] = sig
common = sigs.most_common(1)[0][0] if sigs else None
odd = [p for p, s in sig_of.items() if s != common]
if odd: probs['prefix signature differs'] = odd
print(f"partcheck: {npart} parts expected; LTSB package: {'yes, LTSBFILE ' + lb if lb else 'no'}; levels {nlev0}; "
      f"distinct prefix signatures {len(sigs)}; SOLUTION/nsol {nsol}; LBPRUNE lines {nlb}")
if lb and common:
    print('LB prunes in the prefix (levels <= SPL, same in every part): ' + ' '.join(f'{t}:{v}' for t, v in enumerate(common[spl + 1:])))
    print('LB prunes below the split (disjoint sums): ' + ' '.join(f'{t}:{lbsum[t]}' for t in range(spl + 1, (nlev0 or 0) + 1)))
if ngen: print(f"rc14g informational lines 'lwe11: generated lane loops for levels ...' (accepted): {ngen}")
if unknown: print(f'unknown line types: {dict(unknown)}')
for k, v in probs.items(): print(f'PROBLEM {k}: {len(v)} parts {v[:10]}')
print(f'solutions (DONE nsol + SOLUTION lines): {nsol}')
print('PARTCHECK ' + ('OK' if not probs else 'FAIL'))
