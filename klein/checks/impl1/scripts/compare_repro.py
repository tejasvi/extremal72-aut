"""Compare the audit reproduction (re-run directory on the machine, copied to repro/) with the original lwe outputs (boxcopy/).
R2: audited engine with the original split (4, 64, PART) on the 7 split instances: every part's LEVEL lines must equal
    the original part's.  R1: unsplit run-binary copy on 3_5 and 21_2: per-level totals must equal the sums over the
    64 original parts (levels <= 4 counted once).  R3: audited engine unsplit on the other 112: LEVEL lines must equal
    outall.  Also aggregates the audit counters KILLW (kills by constraint weight), KILLM (kills by method) and
    NAIVECHECK (sampled nodes re-evaluated naively)."""
import os, re, glob, collections
HERE = os.path.dirname(os.path.abspath(__file__))
B = HERE + '/../boxcopy'
R = HERE + '/../repro'


def lev(fn):
    L = {}; done = None; sols = 0; extra = collections.Counter(); chk = None
    for l in open(fn):
        if l.startswith('LEVEL '):
            f = l.split(); L[int(f[1])] = (int(f[3]), int(f[5]), int(f[7]), int(f[9]))
        elif l.startswith('DONE lwe'): done = l.split()
        elif l.startswith('SOLUTION'): sols += 1
        elif l.startswith('KILLW'):
            for tok in l.split()[1:]:
                k, v = tok.split(':'); extra['kill_' + k] += int(v)
        elif l.startswith('KILLM'):
            for tok in l.split()[1:]:
                k, v = tok.split(':'); extra['kill_' + k] += int(v)
        elif l.startswith('NAIVECHECK'):
            f = l.split(); extra['chk_nodes'] += int(f[2]); extra['chk_children'] += int(f[4]); extra['chk_mismatch'] += int(f[6])
        elif l.startswith('CHECK MISMATCH'): extra['CHECK_MISMATCH_LINES'] += 1
    return L, done, sols, extra


tot = collections.Counter(); problems = []
split = {'3_6': 'out', '15_2': 'out', '20_7': 'out', '23_2': 'out', '25_2': 'out', '21_2': 'out', '3_5': 'out35'}
for inst, d in split.items():
    sums = collections.Counter(); upper = None; nparts = 0
    for p in range(64):
        a = f'{R}/a_{inst}_{p}.out'; o = f'{B}/{d}/lw_{inst}_{p}.out'
        Lo, do, so, eo = lev(o)
        for t, (kt, nc, nd, kd) in Lo.items():
            if t >= 5: sums[t] += nd
        upper = {t: Lo[t][2] for t in range(5)}
        if not os.path.exists(a): problems.append(('R2 missing', inst, p)); continue
        La, da, sa, ea = lev(a)
        nparts += 1; tot.update(ea)
        if La != Lo or sa or so or da is None or da[3] != '0': problems.append(('R2 differs', inst, p))
    for r1 in [f'{R}/unsplit_{inst}.out']:
        if os.path.exists(r1):
            Lu, du, su, eu = lev(r1)
            ok = all(Lu[t][2] == upper[t] for t in range(5)) and all(Lu[t][2] == sums[t] for t in range(5, len(Lu))) and su == 0 and du and du[3] == '0'
            print(f'R1 unsplit {inst}: per-level nodes equal to split sums: {ok}; unsplit total {sum(v[2] for v in Lu.values())}, nsol {su}')
            if not ok: problems.append(('R1 differs', inst))
    print(f'R2 {inst}: parts compared {nparts}/64')
n3 = 0
for f in sorted(glob.glob(f'{B}/outall/lw_*.out')):
    inst = re.search(r'lw_(\d+_\d+)\.out', f).group(1)
    a = f'{R}/u_{inst}.out'
    if not os.path.exists(a): problems.append(('R3 missing', inst)); continue
    La, da, sa, ea = lev(a); Lo, do, so, eo = lev(f)
    n3 += 1; tot.update(ea)
    if La != Lo or sa or da is None or da[3] != '0': problems.append(('R3 differs', inst))
print('R3 unsplit instances compared', n3)
print('audit counters', dict(sorted(tot.items())))
print('problems', len(problems), problems[:20])
