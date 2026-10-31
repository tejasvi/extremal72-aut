"""z11_verify.py : rc11 / lwe11b5 validation verdict from the pulled box logs (logs/boxpull/z11g = hostM, <CPU>;
logs/boxpull/z11z = fleet04, <CPU>).  Every row is checked; hashes are recomputed from the raw logs.
(a) without LTSBFILE: std (vs lwe8, probes), self-check, forced paths, production (vs lwe8), samples (vs lwe10),
    package self-checks;  (b) QR48 key controls: rc11 = lwe11b5 = lwe10b with LTSB (LEVEL/DONE/SOL/LBPRUNE), same
    without LTSB, self-check runs, H-closure of the representatives = plain set (QRCLOSURE=1 runs the closure check);
(c) exact parts: rc11 = lwe11b5 = lwe10b with LTSB, probes equal;  (d) self-check runs passed."""
import os, re, sys, glob, hashlib, collections
A = '<HOME>/c72/c2opt/alg'
G, Z = f'{A}/logs/boxpull/z11g', f'{A}/logs/boxpull/z11z'
S = '<HOME>/c72/c2opt/struct/runs'
bad = []


def h(fn, lb=True):
    pre = ('LEVEL', 'DONE', 'SOL', 'LBPRUNE') if lb else ('LEVEL', 'DONE', 'SOL')
    return hashlib.sha256(''.join(re.sub(r'time [0-9]*s', '', l) for l in open(fn) if l.startswith(pre)).encode()).hexdigest()[:16]


def err_ok(fn, need_lb):
    e = open(fn).read() if os.path.exists(fn) else ''
    return 'LWE11CHECK passed' in e and (not need_lb or 'LB check' in e)


# (c) exact parts
ex = collections.defaultdict(dict)
for root, box in ((G, 'g'), (Z, 'z')):
    for f in glob.glob(f'{root}/exact/*.log'):
        b = os.path.basename(f)[:-4]; code, n, p, eng, mode = b.split('_')
        ex[(code, n, p, mode)][eng] = f
ncmp = 0
for (code, n, p, mode), d in sorted(ex.items()):
    if mode == 'lb':
        if set(d) != {'lwe10b', 'lwe11b5', 'lwe11rc11', 'lwe11b5f', 'lwe11rc11f'}: bad.append(('exact missing', code, p, sorted(d))); continue
        hs = {e: h(f) for e, f in d.items()}
        if len(set(hs.values())) != 1: bad.append(('exact differ', code, p, hs))
        if not any(l.startswith('LBPRUNE') for l in open(d['lwe11rc11'])): bad.append(('no LBPRUNE', code, p))
        ncmp += 1
    elif mode == 'lbchk':
        if set(d) != {'lwe11b5', 'lwe11rc11'}: bad.append(('chk missing', code, p, sorted(d))); continue
        if h(d['lwe11b5']) != h(d['lwe11rc11']): bad.append(('chk differ', code, p))
        for e, f in d.items():
            if not err_ok(f[:-4] + '.err', True): bad.append(('chk failed', code, p, e))
    elif mode == 'probe':
        tot = {e: [l for l in open(f) if l.startswith('TOTAL')] for e, f in d.items()}
        if len(d) != 3 or len(set(tuple(v) for v in tot.values())) != 1: bad.append(('probe differ', code, tot))
print('exact lb parts compared (lwe10b = lwe11b5 = rc11):', ncmp, '| codes', sorted({k[0] for k in ex}))
# (b) QR48
qr = collections.defaultdict(dict)
for root in (G, Z):
    for f in glob.glob(f'{root}/qr/*.log'):
        b = os.path.basename(f)[:-4]; tag, eng, mode = b.rsplit('_', 2)
        qr[tag][(eng, mode)] = f
nq = 0
for tag, d in sorted(qr.items()):
    lb = [d.get((e, m)) for e, m in (('lwe10b', 'lb'), ('lwe11b5', 'lb'), ('lwe11rc11', 'lb'), ('lwe11b5', 'lbchk'), ('lwe11rc11', 'lbchk'),
                                     ('lwe11b5f', 'lb'), ('lwe11rc11f', 'lb'), ('lwe11b5f', 'lbchk'), ('lwe11rc11f', 'lbchk'))]
    nl = [d.get((e, 'nolb')) for e in ('lwe10b', 'lwe11b5', 'lwe11rc11')]
    if None in lb or None in nl: bad.append(('qr missing', tag, sorted(d))); continue
    if len({h(f) for f in lb}) != 1: bad.append(('qr lb differ', tag))
    if len({h(f) for f in nl}) != 1: bad.append(('qr nolb differ', tag))
    for e in ('lwe11b5', 'lwe11rc11', 'lwe11b5f', 'lwe11rc11f'):
        if not err_ok(d[(e, 'lbchk')][:-4] + '.err', True): bad.append(('qr chk failed', tag, e))
    nq += 1
print('QR48 configurations compared:', nq)
# (a) standard suite
for root, eng, nsamp in ((G, 'lwe11b5', 66), (Z, 'lwe11rc11', 1056)):
    stdall = [l.split() for l in open(f'{root}/STD.txt')]
    for e2 in (eng, eng + 'f'):
        rows = [r for r in stdall if r[1] == e2]
        if len(rows) != 14 or len({r[0] for r in rows}) != 14 or not all('PROBE_OK' in r for r in rows): bad.append(('std', e2))
        for r in rows:
            if h(f'{root}/std/{r[0]}_{r[1]}.log', False) != h(f'{A}/logs/val/std/{r[0]}_lwe8.log', False): bad.append(('std raw', e2, r[0]))
    std = [r for r in stdall if r[1] == eng]
    chk = open(f'{root}/CHECK.txt').read().strip().split('\n')
    if len(chk) != 15 or not all('LWE11CHECK passed' in l and l.endswith('SAME') for l in chk): bad.append(('check', eng))
    frc = open(f'{root}/FORCE.txt').read().strip().split('\n')
    if len(frc) != 15 or not all('LWE11CHECK passed' in l and l.endswith('SAME') for l in frc): bad.append(('force', eng))
    prd = [l.split() for l in open(f'{root}/PROD.txt')]
    # hostM's first 8 PROD summary lines compared against a missing reference path (ref/ -> logs/ link added at 20:18);
    # the verdict uses the raw recheck below for every production part
    if len(prd) != 8 or len({r[0] for r in prd}) != 8: bad.append(('prod', eng))
    for r in prd:
        if h(f'{root}/prod/{r[0]}_{r[1]}.log', False) != h(f'{A}/logs/ref/{r[0]}_lwe8.log', False): bad.append(('prod raw', eng, r[0]))
    smp = collections.defaultdict(list)
    for l in open(f'{root}/SAMPLES.txt'):
        f = l.split(); smp[f[2]].append(f)
    for e, rows in smp.items():
        keys = {(r[0], r[1]) for r in rows}
        if len(keys) != len(rows) or not all(r[7] == 'IDENTICAL' for r in rows): bad.append(('samples', e))
        for d_, b_ in keys:
            if h(f'{root}/struct/{d_}_{b_}_{e}.log', False) != h(f'{S}/{d_}/samples/{b_}.log', False): bad.append(('sample raw', e, d_, b_))
        print(f'samples {e} on {os.path.basename(root)}: {len(keys)} identical to lwe10' if not [x for x in bad if x[0].startswith('sample')] else 'SAMPLE PROBLEM')
    print(f'{eng} on {os.path.basename(root)}: std {len(std)}, check {len(chk)}, force {len(frc)}, prod {len(prd)}')
sc = open(f'{Z}/SCHECK.txt').read().strip().split('\n')
if len(sc) != 33 or not all('LWE11CHECK passed' in l and l.endswith('done 1') for l in sc): bad.append(('scheck',))
print('package self-checks (rc11):', len(sc))
print('PROBLEMS:', bad[:20], len(bad))
