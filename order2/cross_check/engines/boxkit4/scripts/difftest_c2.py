"""Differential tests of engines against lwe8 on plain-C2 packages (audit code).
Every engine gets the same input and environment (LTSHFILE = package sym.ltsh unless --nosym); outputs are compared
after removing the time field of the DONE line: all LEVEL lines, the SOLUTION lines (in order and as a set), the
DONE line, the leaf-prune line, and any STOPPED line.
Modes
  part   PKG SPL NPART P1,P2,...                      parts of the real instance
  pin    PKG L PREFIXFILE NPREF SEED VARIANTS [SPL NPART]
         sub-instances pinned at prefixes (one per line 'PREFIX hi lo') that survive lwe8's own tests at level L;
         VARIANTS: comma list of exact, keepQ (each bad syndrome kept with probability Q), plant (a random completion
         made a solution), plantkeepQ.  With SPL NPART, every part of each sub-instance is run as well and the part
         sums are checked against the unsplit run (levels > SPL disjoint, levels <= SPL equal in every part).
Engines: --eng name=path (repeatable); the first is the reference (lwe8).  Usage examples in the audit notes."""
import sys, os, subprocess, random, argparse, time

PIN = '<HOME>/audit_c2/kit4/scripts/pin.py'


def run(cmd, env, tmo):
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=tmo)
    except subprocess.TimeoutExpired:
        return None, time.time() - t0
    return (r.returncode, r.stdout, r.stderr), time.time() - t0


def norm(out):
    lev, sol, other = [], [], []
    for l in out.split('\n'):
        if l.startswith('LEVEL '): lev.append(l.strip())
        elif l.startswith('SOLUTION'): sol.append(l.split()[1])
        elif l.startswith('DONE'):
            f = l.split(); i = f.index('time'); other.append(' '.join(f[:i] + f[i + 2:]))
        elif l.startswith(('SYMPRUNE', 'STOPPED')): other.append(l.strip())
    return lev, sol, other


def levnodes(lev):
    return [(int(l.split()[1]), int(l.split()[7]), int(l.split()[9])) for l in lev]


def compare(name, ref, got):
    return ref == got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode'); ap.add_argument('pkg'); ap.add_argument('rest', nargs='*')
    ap.add_argument('--eng', action='append', required=True)
    ap.add_argument('--tag', default='t'); ap.add_argument('--work', required=True)
    ap.add_argument('--tmo', type=int, default=3000); ap.add_argument('--nosym', action='store_true')
    a = ap.parse_args()
    engs = [e.split('=', 1) for e in a.eng]
    env = dict(os.environ)
    if not a.nosym: env['LTSHFILE'] = os.path.join(a.pkg, 'sym.ltsh')
    inst = os.path.join(a.pkg, 'inst.txt')
    os.makedirs(a.work, exist_ok=True)
    nt = nbad = 0

    def one(label, instf, args):
        nonlocal nt, nbad
        res = {}
        for name, path in engs:
            r, dt = run([path, instf] + args, env, a.tmo)
            if r is None: res[name] = ('TIMEOUT', dt); continue
            rc, out, err = r
            res[name] = ((rc, norm(out), err.strip()[:200]), dt)
        refname = engs[0][0]; ref = res[refname][0]
        line = [label]
        ok = ref != 'TIMEOUT' and ref[0] == 0
        for name, _ in engs:
            r, dt = res[name]
            if r == 'TIMEOUT': line.append(f'{name}=TIMEOUT'); ok = False; continue
            same = (r[0] == 0 and r[1] == ref[1]) if ref != 'TIMEOUT' else False
            line.append(f'{name}={"same" if same else "DIFF"}:{dt:.1f}s')
            if not same: ok = False
        if ref != 'TIMEOUT':
            ln = levnodes(ref[1][0]); line.append(f'nodes={sum(x[1] for x in ln)} sols={len(ref[1][1])}')
        nt += 1; nbad += (not ok)
        print(('OK ' if ok else 'MISMATCH ') + ' '.join(line), flush=True)
        if not ok:
            for name, _ in engs:
                r = res[name][0]
                if r != 'TIMEOUT' and ref != 'TIMEOUT' and r[1] != ref[1]:
                    diffs = [(x, y) for x, y in zip(ref[1][0], r[1][0]) if x != y][:3]
                    print('   ', name, 'rc', r[0], 'err', r[2], 'first level diffs', diffs, 'other', r[1][2], 'vs', ref[1][2], flush=True)
        return ref

    if a.mode == 'part':
        spl, npart, parts = a.rest[0], a.rest[1], a.rest[2].split(',')
        for p in parts: one(f'{a.tag} part {p}/{npart} spl {spl}', inst, [spl, npart, p])
    elif a.mode == 'pin':
        L, pfile, npref, seed, variants = int(a.rest[0]), a.rest[1], int(a.rest[2]), int(a.rest[3]), a.rest[4].split(',')
        split = (a.rest[5], a.rest[6]) if len(a.rest) > 6 else None
        rnd = random.Random(seed)
        prefs = [l.split() for l in open(pfile) if l.startswith('PREFIX')]
        rnd.shuffle(prefs)
        with open(inst) as fh: N = int(fh.readline().split()[0]); vs = list(map(int, fh.readline().split()))
        for pi, (_, hi, lo) in enumerate(prefs[:npref]):
            x0 = (int(hi, 16) << 64) | int(lo, 16)
            for var in variants:
                extra = []
                if var.startswith('keep'): extra = ['--keep', var[4:], str(rnd.getrandbits(30))]
                if var.startswith('plant'):
                    x1 = x0 | (rnd.getrandbits(N - vs[L]) << vs[L])
                    extra = ['--plant', f'{x1:x}'] + (['--keep', var[9:], str(rnd.getrandbits(30))] if var.startswith('plantkeep') else [])
                sub = os.path.join(a.work, f'sub_{a.tag}.txt')
                subprocess.run([sys.executable, '-I', PIN, inst, sub, str(L), f'{x0:x}'] + extra, check=True)
                ref = one(f'{a.tag} pin L{L} pref {pi} {var}', sub, [])
                if split and ref != 'TIMEOUT':
                    spl, npart = split
                    tot = {}; sols = []; upper = None; okp = True
                    reflev = levnodes(ref[1][0])
                    for p in range(int(npart)):
                        rp = one(f'{a.tag} pin L{L} pref {pi} {var} part {p}/{npart} spl {spl}', sub, [spl, npart, str(p)])
                        if rp == 'TIMEOUT': okp = False; continue
                        sols += rp[1][1]
                        for (t, nd, kd) in levnodes(rp[1][0]):
                            if t > int(spl): tot[t] = tot.get(t, 0) + nd
                            elif nd != reflev[t][1]: okp = False
                    if any(tot.get(t, 0) != nd for (t, nd, kd) in reflev if t > int(spl)) or sorted(sols) != sorted(ref[1][1]) or len(sols) != len(set(sols)):
                        okp = False
                    nt += 1; nbad += (not okp)
                    print(('OK ' if okp else 'MISMATCH ') + f'{a.tag} pin L{L} pref {pi} {var} SPLITSUM spl {spl} npart {npart}', flush=True)
    print(f'SUMMARY {a.tag} tests {nt} mismatches {nbad}', flush=True)


if __name__ == '__main__':
    main()
