"""Copy of the C2xC2 audit diff_test.py (paths changed): lwe8 WITHOUT symmetry vs the naive engine on pinned sub-instances.
Differential test lwe vs naive on pinned sub-instances of a real instance.
For NP random prefixes reaching level L (naive probe): pin, then compare lwe and naive (all LEVEL lines, solution
sets) on (a) the exact subtree, (b) a planted relaxation (a random completion X1 of the prefix made a solution by
deleting its syndrome from every bad set of level >= L), (c) a random relaxation (each bad syndrome kept with
probability Q) and (d) split runs of lwe (SPL, NPART) on (b): union of parts == unsplit, node sums agree.
Usage: diff_test.py INSTANCE L NP SEED Q LWEBIN TAG"""
import sys, subprocess, random, os
S = '<HOME>/audit_c2/kit/scripts'
W = '<HOME>/audit_c2/kit/work'


TMO = int(os.environ.get('DIFF_TIMEOUT', '600'))


def run(cmd):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=TMO)
    except subprocess.TimeoutExpired:
        return '', 'TIMEOUT'
    return r.stdout, r.returncode


def parse(out):
    sols = sorted(l.split()[1] for l in out.split('\n') if l.startswith('SOLUTION'))
    lev = [tuple(int(x) for x in (l.split()[1], l.split()[7], l.split()[9])) for l in out.split('\n') if l.startswith('LEVEL')]
    done = [l for l in out.split('\n') if l.startswith('DONE')]
    return sols, lev, done


def main():
    inst, L, NP, seed, Q, lwebin, tag = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), sys.argv[6], sys.argv[7]
    rnd = random.Random(seed)
    hdr = open(inst).readline().split(); N = int(hdr[0])
    out, _ = run([f'{S}/naive', inst, 'probe', str(L), str(seed), str(NP)])
    prefs = [(int(l.split()[1], 16) << 64) | int(l.split()[2], 16) for l in out.split('\n') if l.startswith('PREFIX')]
    stats = dict(tests=0, mismatches=0, sols=0, nodes=0, planted_found=0, planted=0, split_ok=0, split_bad=0)
    sub = f'{W}/sub_{tag}.txt'
    with open(inst) as fh: fh.readline(); vsL = int(fh.readline().split()[L])
    for pi, x0 in enumerate(prefs):
        variants = [('exact', [])]
        x1 = x0 | (rnd.getrandbits(N - vsL) << vsL)
        variants.append(('plant', ['--plant', f'{x1:x}']))
        variants.append(('keep', ['--keep', str(Q), str(rnd.getrandbits(30))]))
        variants.append(('plantkeep', ['--plant', f'{x1:x}', '--keep', str(Q), str(rnd.getrandbits(30))]))
        if os.environ.get('ADDBAD'):
            variants.append(('addbad', ['--addbad', os.environ['ADDBAD'], str(rnd.getrandbits(30)), '--keep', str(Q), str(rnd.getrandbits(30))]))
        for name, extra in variants:
            subprocess.run([sys.executable, '-I', f'{S}/pin.py', inst, sub, str(L), f'{x0:x}'] + extra, check=True)
            o1, rc1 = run([lwebin, sub]); o2, rc2 = run([f'{S}/naive', sub, 'count'])
            if rc1 == 'TIMEOUT' or rc2 == 'TIMEOUT':
                stats['timeouts'] = stats.get('timeouts', 0) + 1; continue
            s1, l1, d1 = parse(o1); s2, l2, d2 = parse(o2)
            stats['tests'] += 1
            ok = (rc1 == 0 and rc2 == 0 and s1 == s2 and l1 == l2 and d1 and d2)
            if not ok:
                stats['mismatches'] += 1
                print('MISMATCH', tag, pi, name, f'{x0:x}', rc1, rc2, len(s1), len(s2), [a for a, b in zip(l1, l2) if a != b][:3], flush=True)
            stats['sols'] += len(s1); stats['nodes'] += sum(x[1] for x in l1)
            if name.startswith('plant'):
                stats['planted'] += 1
                x1s = x1 >> vsL
                if f'{x1s:032x}' in s1: stats['planted_found'] += 1
                else: print('PLANT NOT FOUND', tag, pi, name, flush=True)
            if name in ('plant', 'plantkeep') and len(s1) > 0:
                # split runs at a level >= L where there are nodes
                for spl in sorted(set([L, min(L + 2, len(l1) - 1)])):
                    for npart in (3, 7):
                        us = []; tot = [0] * len(l1); okp = True
                        for p in range(npart):
                            op, rcp = run([lwebin, sub, str(spl), str(npart), str(p)])
                            if rcp == 'TIMEOUT': okp = False
                            sp, lp, dp = parse(op)
                            us += sp
                            if rcp != 0 or not dp: okp = False
                            for t, (lvl, nd, kd) in enumerate(lp):
                                if t > spl: tot[t] += nd
                                elif nd != l1[t][1]: okp = False
                        if sorted(us) != s1 or any(tot[t] != l1[t][1] for t in range(spl + 1, len(l1))) or len(us) != len(set(us)): okp = False
                        stats['split_ok' if okp else 'split_bad'] += 1
                        if not okp: print('SPLIT MISMATCH', tag, pi, name, spl, npart, flush=True)
    print('SUMMARY', tag, os.path.basename(inst), 'L', L, 'prefixes', len(prefs), stats, flush=True)


if __name__ == '__main__':
    main()
