"""Seeded selection of whole production parts of explore's runs for re-runs with the audit's portable lwe8 build.
part_i = int(sha256('coverage-check-xnat-' + code + '-' + str(i)), 16) mod NPART, i = 0, 1, ...; per binary class the first
K parts whose production time is <= TMAX seconds (light-work limit on the main VM; the cap is reported).
Binary classes per part from RUN_SUMMARY.txt ranges (Y4, Y1b) or the whole run."""
import hashlib, re, os, sys
R = '<HOME>/c72/explore/runs2'
K = int(sys.argv[1]) if len(sys.argv) > 1 else 2
TMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 200
def y1b_class(q):
    if 0 <= q <= 3999 or 6000 <= q <= 7999: base = 'hostB lwe11 native 5326c666'
    else: base = 'hostC lwe11 native 5326c666'
    if 6980 <= q <= 6999 or 7907 <= q <= 7999: return 'local lwe10 portable 09f2716d'
    if 7480 <= q <= 7906 or 5660 <= q <= 5999: return 'local lwe11 portable b29ded1c'
    return base
RUNS = {  # code: (parts dir, NPART, class function)
    'y22': ('parts_hostB', 4000, lambda q: 'hostB lwe8 native 0365005b'),
    'y23': ('parts_hostB', 4000, lambda q: 'hostB lwe10 native ee20e13c'),
    'y4': ('parts_hostC', 4000, lambda q: 'hostC lwe8 native 0365005b' if q <= 3639 else 'local lwe11 portable b29ded1c'),
    'y5b': ('parts_hostC', 4000, lambda q: 'hostC lwe11 native 5326c666'),
    'y1b': ('parts_all', 8000, y1b_class),
    'y8': ('parts', 500, lambda q: 'local lwe8 portable 149ce3f3'),
}
for code, (d, npart, cls) in RUNS.items():
    got = {}; skipped = {}; seen = set(); i = 0
    while i < 20000:
        q = int(hashlib.sha256(f'coverage-check-xnat-{code}-{i}'.encode()).hexdigest(), 16) % npart; i += 1
        if q in seen: continue
        seen.add(q)
        c = cls(q)
        if len(got.get(c, [])) >= K: 
            if all(len(v) >= K for v in got.values()) and len(seen) > 400: break
            continue
        m = re.search(r'time (\d+)s', open(f'{R}/{code}/{d}/p{q}.log').read())
        t = int(m.group(1))
        if t > TMAX: skipped[c] = skipped.get(c, 0) + 1; continue
        got.setdefault(c, []).append((q, t))
    for c in sorted(got):
        print(code, c.replace(' ', '_'), ' '.join(f'{q}:{t}' for q, t in got[c]), f'(skipped over {TMAX}s: {skipped.get(c, 0)})')
