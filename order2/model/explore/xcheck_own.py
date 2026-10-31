"""xcheck for explore's own box runs: compare lwe8 reruns of 8 seeded parts (delivered by fleet under
XROOT/<pkg>/: p<k>.log, SHA256SUMS, ORIGIN.tsv) with the production logs.  Same rule and comparison as
src/xcheck_cmp.py: part_i = int(sha256("c2-xcheck-"+pkg+"-"+str(i)),16) mod NPART, duplicates skipped, until 8;
LEVEL/DONE/SOLUTION/SYMPRUNE lines with 'time <n>s' stripped.  Production ran on <CPU> (hostB, hostC, the main VM),
so the reruns must come from another family (not famA/famB).
Usage: xcheck_own.py PKG   (writes nothing; print to runs2/<pkg>/XCHECK8.txt)"""
import glob, hashlib, os, re, subprocess, sys

pkg = sys.argv[1]
R = '<HOME>/c72/explore/runs2'
XROOT = '<HOME>/c72/fleet/results_xc2e'
PROD = {'y8': 'parts', 'y22': 'parts_hostB', 'y23': 'parts_hostB', 'y4': 'parts_hostC', 'y5b': 'parts_hostC',
        'y1b': 'parts_all'}[pkg]
LWE8 = '149ce3f36e48d07ea266af31241d9439f22e433ab9a3074097bb9d99dd7cd8fc'
npart = int(re.search(r'^NPART (\d+)', open(f'{R}/{pkg}/PLAN.txt').read(), re.M).group(1))
sel = []; i = 0
while len(sel) < 8:
    k = int(hashlib.sha256(f'c2-xcheck-{pkg}-{i}'.encode()).hexdigest(), 16) % npart
    if k not in sel: sel.append(k)
    i += 1
X = f'{XROOT}/{pkg}'
print(f'xcheck for {pkg} (NPART {npart}); seeded selection {sel}; reruns in {X}; production logs in {R}/{pkg}/{PROD}')


def key(fn):
    return ''.join(re.sub(r'time \d+s', '', l) for l in open(fn)
                   if l.startswith(('LEVEL', 'DONE', 'SOLUTION', 'SYMPRUNE')))


probs = []
if os.path.exists(f'{X}/SHA256SUMS'):
    rc = subprocess.run(['sha256sum', '-c', '--quiet', 'SHA256SUMS'], cwd=X, capture_output=True, text=True)
    print(f'SHA256SUMS: rc {rc.returncode}')
    if rc.returncode: probs.append('SHA256SUMS')
else:
    probs.append('no SHA256SUMS')
orig = {}
if os.path.exists(f'{X}/ORIGIN.tsv'):
    for l in open(f'{X}/ORIGIN.tsv'):
        c = l.rstrip('\n').split('\t')
        if l.startswith('#') or len(c) < 5: continue
        orig[int(c[0].lstrip('p'))] = c
ok = 0; bad = []; missing = []
for k in sel:
    f = f'{X}/p{k}.log'
    if not os.path.exists(f) or '\nDONE' not in '\n' + open(f).read() or 'STOPPED' in open(f).read():
        missing.append(k); continue
    o = orig.get(k)
    if not o: probs.append(f'p{k}: no ORIGIN row')
    else:
        box, mtype, eng, esha = o[1], o[2], o[3], o[4]
        if esha != LWE8: probs.append(f'p{k}: engine {eng} {esha[:12]}')
        if len(o) > 5 and o[5].strip() and o[5].strip().split(':')[-1] not in (LWE8, '-'):
            probs.append(f'p{k}: measured exe {o[5][:20]}')   # fleet's measured /proc/PID/exe sha column
        if mtype.split('-')[0] in ('famA', 'famB'): probs.append(f'p{k}: <CPU> family {mtype}')
    ka, kb = key(f), key(f'{R}/{pkg}/{PROD}/p{k}.log')
    ha, hb = (hashlib.sha256(x.encode()).hexdigest()[:16] for x in (ka, kb))
    tm = re.search(r'^DONE .* time (\d+)s', open(f).read(), re.M)
    print(f'p{k}: rerun on {o[1] if o else "?"} {o[2] if o else "?"} time {tm.group(1) if tm else "?"}s; key sha {ha} '
          f'production {hb} {"IDENTICAL" if ka == kb else "DIFFERENT"}')
    if ka == kb: ok += 1
    else: bad.append(k)
print(f"setup (lwe8 149ce3f3, not <CPU>, SHA256SUMS, ORIGIN rows): {'OK' if not probs else probs}")
print(f'xcheck {ok}/8 identical' + (f'; DIFFERENT: {bad}' if bad else '') +
      (f'; not yet available: {missing}' if missing else '') + ('; SETUP NOT OK' if probs else ''))
