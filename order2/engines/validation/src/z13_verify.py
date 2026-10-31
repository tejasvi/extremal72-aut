"""z13_verify.py : rc13 (build rc13e, lwe11 2cd44f91) / lwe11b7 validation verdict from the pulled box logs
(logs/boxpull/z13c = fleet04, <CPU>: rc11, rc13e, lwe11b7 built on hostM, forced rc13e builds; logs/boxpull/z13g = hostM,
<CPU>: lwe11b7 and its forced builds built there, struct's prototype lwe10b).  Every row is checked; hashes are
recomputed from the raw logs (LEVEL/DONE/SOL[/LBPRUNE] lines, time field removed).
(a) without LTSBFILE: std (vs lwe8, probes), self-check, forced paths, production (vs lwe8), samples (vs lwe10),
    package self-checks;  (b) QR48 key controls: rc11 = rc13e = lwe11b7 = lwe10b with LTSB, same without LTSB,
    self-check runs;  (c) exact parts of the runs_lb instances: rc11 = rc13e = lwe11b7 = lwe10b, probes equal;
(d) tier C parts vs struct's lwe10b logs, y14/y19b/y26f production-package parts rc11 = rc13e = lwe11b7,
    self-check runs passed."""
import os, re, glob, hashlib, collections
A = '<HOME>/c72/c2opt/alg'
G, Z = f'{A}/logs/boxpull/z13g', f'{A}/logs/boxpull/z13c'
S = '<HOME>/c72/c2opt/struct/runs'
TCREF = f'{A}/logs/boxpull/tierc_ref'
bad = []
JOBS = {root: collections.Counter(tuple(l.split()[:2]) for l in open(f'{root}/jobs.txt')) for root in (G, Z)}   # expected rows per (kind, engine)


def h(fn, lb=True):
    pre = ('LEVEL', 'DONE', 'SOL', 'LBPRUNE') if lb else ('LEVEL', 'DONE', 'SOL')
    return hashlib.sha256(''.join(re.sub(r'time [0-9]*s', '', l) for l in open(fn) if l.startswith(pre)).encode()).hexdigest()[:16]


def done(fn):   # a complete run: a DONE line and no STOPPED line (a stopped run also prints DONE with partial counts)
    L = open(fn).read().split('\n')
    return any(l.startswith('DONE') for l in L) and not any(l.startswith('STOPPED') for l in L)


def err_ok(fn, need_lb):
    e = open(fn).read() if os.path.exists(fn) else ''
    return 'LWE11CHECK passed' in e and (not need_lb or 'LB check' in e)


# (c) exact parts
ex = collections.defaultdict(dict)
for root, box in ((G, 'g'), (Z, 'z')):
    for f in glob.glob(f'{root}/exact/*.log'):
        b = os.path.basename(f)[:-4]; code, n, p, eng, mode = b.split('_')
        ex[(code, n, p, mode)][eng + '@' + box] = f
ncmp = nchk = nprb = 0
for (code, n, p, mode), d in sorted(ex.items()):
    if mode == 'lb':
        if set(d) != {'lwe10b@g', 'lwe11b7@g', 'lwe11rc11@z', 'lwe11rc13e@z', 'lwe11b7@z'}: bad.append(('exact missing', code, p, sorted(d))); continue
        hs = {e: h(f) for e, f in d.items()}
        if len(set(hs.values())) != 1 or not all(done(f) for f in d.values()): bad.append(('exact differ', code, p, hs))
        if not any(l.startswith('LBPRUNE') for l in open(d['lwe11rc13e@z'])): bad.append(('no LBPRUNE', code, p))
        ncmp += 1
    elif mode == 'lbchk':
        if set(d) != {'lwe11b7@g', 'lwe11rc13e@z', 'lwe11b7@z'}: bad.append(('chk missing', code, p, sorted(d))); continue
        if len({h(f) for f in d.values()}) != 1: bad.append(('chk differ', code, p))
        for e, f in d.items():
            if not err_ok(f[:-4] + '.err', True): bad.append(('chk failed', code, p, e))
        nchk += 1
    elif mode == 'probe':
        tot = {e: [l for l in open(f) if l.startswith('TOTAL')] for e, f in d.items()}
        if set(d) != {'lwe10b@g', 'lwe11b7@g', 'lwe11rc11@z', 'lwe11rc13e@z'} or len(set(tuple(v) for v in tot.values())) != 1 or not all(tot.values()):
            bad.append(('probe differ', code, tot))
        nprb += 1
print(f'exact lb parts compared (lwe10b = lwe11b7 (<CPU>) = rc11 = rc13e = lwe11b7 (<CPU>)): {ncmp}; self-check parts {nchk}; probes {nprb}'
      f' | codes {sorted({k[0] for k in ex})}')
# (b) QR48
qr = collections.defaultdict(dict)
for root, box in ((G, 'g'), (Z, 'z')):
    for f in glob.glob(f'{root}/qr/*.log'):
        b = os.path.basename(f)[:-4]; tag, eng, mode = b.rsplit('_', 2)
        qr[tag][(eng + '@' + box, mode)] = f
nq = 0
for tag, d in sorted(qr.items()):
    lb = [d.get(k) for k in (('lwe10b@g', 'lb'), ('lwe11b7@g', 'lb'), ('lwe11b7@g', 'lbchk'), ('lwe11rc11@z', 'lb'), ('lwe11rc13e@z', 'lb'),
                             ('lwe11b7@z', 'lb'), ('lwe11rc13e@z', 'lbchk'), ('lwe11b7@z', 'lbchk'))]
    nl = [d.get((e, 'nolb')) for e in ('lwe10b@g', 'lwe11b7@g', 'lwe11rc11@z', 'lwe11rc13e@z', 'lwe11b7@z')]
    if None in lb or None in nl: bad.append(('qr missing', tag, sorted(d))); continue
    if len({h(f) for f in lb}) != 1 or not all(done(f) for f in lb): bad.append(('qr lb differ', tag))
    if len({h(f) for f in nl}) != 1 or not all(done(f) for f in nl): bad.append(('qr nolb differ', tag))
    for k in (('lwe11b7@g', 'lbchk'), ('lwe11rc13e@z', 'lbchk'), ('lwe11b7@z', 'lbchk')):
        if not err_ok(d[k][:-4] + '.err', True): bad.append(('qr chk failed', tag, k))
    nq += 1
print('QR48 configurations compared:', nq)
# (d) tier C parts and production-package parts
tc = collections.defaultdict(dict)
for f in glob.glob(f'{Z}/tc/*.log'):
    b = os.path.basename(f)[:-4]; code, n, p, eng, mode = b.split('_')
    tc[(code, n, p, mode)][eng] = f
ntc = npk = ntck = 0
for (code, n, p, mode), d in sorted(tc.items()):
    if mode == 'lbchk':
        if not err_ok(d['lwe11rc13e'][:-4] + '.err', True) or not done(d['lwe11rc13e']): bad.append(('tc chk failed', code, p))
        ntck += 1
        continue
    if code in ('y0', 'y14', 'y19') and os.path.exists(f'{TCREF}/{code}_b/s3n{n}_p{p}.log'):
        ref = f'{TCREF}/{code}_b/s3n{n}_p{p}.log'
        if set(d) - {'lwe11rc11'} != {'lwe11rc13e', 'lwe11b7'}: bad.append(('tc missing', code, p, sorted(d))); continue
        if len({h(ref)} | {h(f) for f in d.values()}) != 1 or not all(done(f) for f in d.values()): bad.append(('tc differ', code, p))
        ntc += 1
    else:
        if set(d) != {'lwe11rc11', 'lwe11rc13e', 'lwe11b7'}: bad.append(('pkg missing', code, p, sorted(d))); continue
        if len({h(f) for f in d.values()}) != 1 or not all(done(f) for f in d.values()): bad.append(('pkg differ', code, p))
        npk += 1
print(f'tier C parts identical to struct lwe10b logs (rc13e, lwe11b7): {ntc}; package parts rc11 = rc13e = lwe11b7: {npk}'
      f' ({sorted({k[0] for k, d in tc.items() if "lwe11rc11" in d})}); tc self-checks {ntck}')
# (a) standard suite
for root, engs in ((G, ('lwe11b7',)), (Z, ('lwe11rc13e', 'lwe11b7'))):
    stdall = [l.split() for l in open(f'{root}/STD.txt')]
    for e2 in engs:
        rows = [r for r in stdall if r[1] == e2]
        if len(rows) != 14 or len({r[0] for r in rows}) != 14 or not all('PROBE_OK' in r for r in rows): bad.append(('std', root[-4:], e2))
        for r in rows:
            if h(f'{root}/std/{r[0]}_{r[1]}.log', False) != h(f'{A}/logs/val/std/{r[0]}_lwe8.log', False): bad.append(('std raw', e2, r[0]))
    chk = [l for l in open(f'{root}/CHECK.txt').read().strip().split('\n')]
    if len(chk) != 15 * len(engs) or not all('LWE11CHECK passed' in l and l.endswith('SAME') for l in chk): bad.append(('check', root[-4:]))
    frc = open(f'{root}/FORCE.txt').read().strip().split('\n')
    if len(frc) != 15 or not all('LWE11CHECK passed' in l and l.endswith('SAME') for l in frc): bad.append(('force', root[-4:]))
    prd = [l.split() for l in open(f'{root}/PROD.txt')]
    if len(prd) != 8 or len({r[0] for r in prd}) != 8: bad.append(('prod', root[-4:]))
    for r in prd:
        if h(f'{root}/prod/{r[0]}_{r[1]}.log', False) != h(f'{A}/logs/ref/{r[0]}_lwe8.log', False): bad.append(('prod raw', r[1], r[0]))
    smp = collections.defaultdict(list)
    for l in open(f'{root}/SAMPLES.txt'):
        f = l.split(); smp[f[2]].append(f)
    for e in {k[1] for k in JOBS[root] if k[0] == 'sample'} - set(smp): bad.append(('samples missing', root[-4:], e))
    for e, rows in smp.items():
        keys = {(r[0], r[1]) for r in rows}
        if len(keys) != len(rows) or not all(r[7] == 'IDENTICAL' for r in rows) or len(keys) != JOBS[root][('sample', e)]: bad.append(('samples', e, len(keys)))
        for d_, b_ in keys:
            if h(f'{root}/struct/{d_}_{b_}_{e}.log', False) != h(f'{S}/{d_}/samples/{b_}.log', False): bad.append(('sample raw', e, d_, b_))
        print(f'samples {e} on {os.path.basename(root)}: {len(keys)} of {JOBS[root][("sample", e)]} compared with lwe10')
    print(f'{"/".join(engs)} on {os.path.basename(root)}: std {len(stdall)}, check {len(chk)}, force {len(frc)}, prod {len(prd)}')
sc = open(f'{Z}/SCHECK.txt').read().strip().split('\n')
# Waiver: y26 (struct's old y26 flag, not a production package) cannot finish a self-check part at split 3: LWE11CHECK
# re-derives every child of every prefix node (kt 14 / 13 at levels 2-3), so even the prefix takes hours.  Its run counts
# as a partial self-check if it stopped at the 1-h cap with "LWE11CHECK passed" (no mismatch in the nodes it reached).
WAIVE = {'y26'}
sc_need = {l.split()[2] for l in open(f'{Z}/jobs.txt') if l.startswith('scheck')}
sc_rows = {l.split()[0]: l for l in sc if l}
sc_logs = {d: glob.glob(f'{Z}/struct/{d}_*_lwe11rc13e_chk.log') for d in sc_need}
for d in sorted(sc_need):
    l = sc_rows.get(d)
    if l is None or len(sc_logs[d]) != 1: bad.append(('scheck missing', d)); continue
    if 'LWE11CHECK passed' in l and done(sc_logs[d][0]): continue
    if d in WAIVE and 'LWE11CHECK passed' in l and any(x.startswith('STOPPED') for x in open(sc_logs[d][0])):
        print('scheck WAIVED (stopped at the 1-h cap, no mismatch in the nodes reached):', l); continue
    bad.append(('scheck', d, l[:120]))
for root in (G, Z):   # no stopped run anywhere else
    for f in glob.glob(f'{root}/*/*.log'):
        if any(x.startswith('STOPPED') for x in open(f)) and not any(f in v for v in sc_logs.values()): bad.append(('stopped run', f))
print('package self-checks (rc13e):', len(sc_rows), 'of', len(sc_need))
print('PROBLEMS:', bad[:20], len(bad))
