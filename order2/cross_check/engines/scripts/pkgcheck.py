"""Independent instance checks of the production packages on their CURRENT files (audit code, 2026-10-26).
Per package: the production files (fleet snapshot fleet/pkgs/<pkg>, or explore runs2/<pkg>), their sha256 and the
package's INPUTS.sha256 verification; for LB packages the parametrisation (inst.txt.pkl) of the base package named in
BUILD.txt, whose flag.txt must equal the package's; then indep_c2.py (every constraint, coverage, weight 14),
symcheck.py (every sym.ltsh table) and e2e_c2.py (genuine codes).  Usage: pkgcheck.py PKG [PKG ...]"""
import sys, os, re, subprocess, hashlib, time
A = '<HOME>/c72/audit/c2audit/engine-check'; S = A + '/scripts'; OUT = A + '/pkgcheck'
FLEET = '<HOME>/c72/fleet/pkgs'; EXPL = '<HOME>/c72/explore/runs2'
STRUCT = '<HOME>/c72/c2opt/struct/runs'
NRANDB, NRAND, SEED = 20, 10, 2610


def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def run(cmd, log, tmo):
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=tmo)
        out, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        out, rc = 'TIMEOUT\n', -1
    open(log, 'w').write(out)
    return rc, out, time.time() - t0


for pkg in sys.argv[1:]:
    src = os.path.join(FLEET, pkg) if os.path.isdir(os.path.join(FLEET, pkg)) else os.path.join(EXPL, pkg)
    ci = int(re.match(r'y(\d+)', pkg).group(1)); d = os.path.join(OUT, pkg); os.makedirs(d, exist_ok=True)
    lines = [f'package {pkg} code {ci} files {src}']
    ok = True
    # INPUTS.sha256 of the production snapshot (entries outside the snapshot, e.g. frozen/, are not files here)
    inp = os.path.join(src, 'INPUTS.sha256')
    if os.path.exists(inp):
        bad = []
        for l in open(inp):
            f = l.split()
            if len(f) == 2 and not f[1].startswith('frozen/') and os.path.exists(os.path.join(src, f[1])):
                if sha(os.path.join(src, f[1])) != f[0]: bad.append(f[1])
        lines.append('INPUTS.sha256: ' + ('all listed snapshot files match' if not bad else 'MISMATCH ' + ' '.join(bad)))
        ok &= not bad
    else:
        lines.append('INPUTS.sha256: none in the snapshot')
    base = None
    if os.path.exists(os.path.join(src, 'BUILD.txt')):
        m = re.search(r'runs/([^/\s]+)/inst\.txt', open(os.path.join(src, 'BUILD.txt')).read())
        base = m.group(1) if m else None
    pkl = os.path.join(src, 'inst.txt.pkl')
    if not os.path.exists(pkl):
        if base is None: lines.append('NO inst.txt.pkl and no base package'); ok = False; pkl = None
        else:
            pkl = os.path.join(STRUCT, base, 'inst.txt.pkl')
            same = sha(os.path.join(STRUCT, base, 'flag.txt')) == sha(os.path.join(src, 'flag.txt'))
            lines.append(f'parametrisation from base package {base}: flag.txt equal to the package flag: {same}')
            ok &= same
    for f in ('inst.txt', 'inst.txt.meta', 'flag.txt', 'key.txt', 'sym.ltsh', 'sym.ltsb'):
        p = os.path.join(src, f)
        if os.path.exists(p):
            dst = os.path.join(d, f)
            if os.path.lexists(dst): os.remove(dst)
            os.symlink(p, dst); lines.append(f'  {f} {sha(p)}')
    if pkl:
        dst = os.path.join(d, 'inst.txt.pkl')
        if os.path.lexists(dst): os.remove(dst)
        os.symlink(pkl, dst); lines.append(f'  inst.txt.pkl {sha(pkl)} ({pkl})')
    res = {}
    for name, cmd, tmo in (('indep', [sys.executable, '-I', S + '/indep_c2.py', d, str(ci)], 540),
                           ('sym', [sys.executable, '-I', S + '/symcheck.py', d, str(ci), str(NRANDB)], 540),
                           ('e2e', [sys.executable, '-I', S + '/e2e_c2.py', d, str(ci), str(NRAND), str(SEED)], 540)):
        rc, out, dt = run(cmd, os.path.join(OUT, 'logs', f'{name}_{pkg}.log'), tmo)
        last = [l for l in out.strip().split('\n') if l.strip()][-1:] or ['']
        passed = rc == 0 and ('PASS' in last[0] or 'TOTALS' in last[0] or 'ok' in last[0].lower()) and 'FAIL' not in out
        res[name] = passed; lines.append(f'{name}: rc {rc} {dt:.0f}s | {last[0][:150]}')
    ok &= all(res.values())
    lines.append(f'RESULT {"PASS" if ok else "FAIL"} {pkg}')
    open(os.path.join(OUT, 'logs', f'pkg_{pkg}.txt'), 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(lines), flush=True)
