"""Run accounting for the box lwe outputs (copied read-only into boxcopy/)."""
import os, re, glob, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
B = HERE + '/../boxcopy'
LI = HERE + '/../../../impl1_runs/lwinst'
def parse(fn):
    txt = open(fn).read()
    lines = txt.split('\n')
    done = [l for l in lines if l.startswith('DONE lwe')]
    sols = [l for l in lines if 'SOLUTION' in l]
    other = [l for l in lines if l and not l.startswith('DONE lwe') and not l.startswith('LEVEL ')]
    lev = {}
    for l in lines:
        if l.startswith('LEVEL '):
            f = l.split(); lev[int(f[1])] = dict(kt=int(f[3]), ncons=int(f[5]), nodes=int(f[7]), kids=int(f[9]))
    return done, sols, other, lev
def hdr(inst):
    with open(f'{LI}/lwf_{inst}.txt') as f:
        N, NLEV, NC = map(int, f.readline().split()); vs = list(map(int, f.readline().split()))
        # count constraints per level
        cnt = collections.Counter()
        for c in range(NC):
            lv, wt, m, nb = map(int, f.readline().split())
            for s in range(m): f.readline()
            f.readline(); cnt[lv] += 1
    return N, NLEV, NC, vs, cnt
classes = [l.split() for l in open(HERE + '/../../../model/lw_all_list.txt').read().split('\n') if l.strip()]
insts = [f'{a}_{b}' for a, b in classes]
assert len(insts) == 119 and len(set(insts)) == 119
problems = []; summary = {}
split_dirs = {'out': ['21_2', '3_6', '23_2', '20_7', '15_2', '25_2'], 'out35': ['3_5']}
splitset = {i: d for d, l in split_dirs.items() for i in l}
for inst in insts:
    N, NLEV, NC, vs, cnt = hdr(inst)
    kt = [vs[t + 1] - vs[t] for t in range(NLEV)]
    if inst in splitset:
        d = splitset[inst]
        files = sorted(glob.glob(f'{B}/{d}/lw_{inst}_*.out'))
        parts = sorted(int(re.search(r'_(\d+)\.out$', f).group(1)) for f in files)
        if parts != list(range(64)): problems.append((inst, 'parts', parts))
        upper = None; tot = 0; kids4 = 0; nodes5 = 0; leaf = 0
        for f in files:
            p = int(re.search(r'_(\d+)\.out$', f).group(1))
            done, sols, other, lev = parse(f)
            if len(done) != 1: problems.append((inst, p, 'done', done)); continue
            fl = done[0].split()
            if not (fl[2] == 'nsol' and fl[3] == '0' and fl[6] == 'split' and fl[7] == '4' and fl[8] == 'part' and fl[9] == f'{p}/64' and fl[10] == 'N' and int(fl[11]) == N):
                problems.append((inst, p, 'doneline', done[0]))
            if sols or other: problems.append((inst, p, 'extra', sols, other))
            if sorted(lev) != list(range(NLEV)): problems.append((inst, p, 'levels'))
            for t in range(NLEV):
                if lev[t]['kt'] != kt[t] or lev[t]['ncons'] != cnt[t]: problems.append((inst, p, 'kt/ncons', t))
            up = tuple((lev[t]['nodes'], lev[t]['kids']) for t in range(4)) + (lev[4]['nodes'],)
            if upper is None: upper = up
            elif up != upper: problems.append((inst, p, 'upper differs'))
            kids4 += lev[4]['kids']; nodes5 += lev[5]['nodes']
            for t in range(5, NLEV):
                if t + 1 < NLEV and lev[t]['kids'] != lev[t + 1]['nodes']: problems.append((inst, p, 'kids!=nodes', t))
            tot += sum(lev[t]['nodes'] for t in range(5, NLEV))
            leaf += lev[NLEV - 1]['kids']
        uniq = sum(upper[t][0] for t in range(4)) + upper[4]
        summary[inst] = dict(files=len(files), nodes_unique=uniq + tot, nodes_lwsum=uniq * 64 + tot, kids4=kids4, nodes5=nodes5, leaf=leaf, lvl4=upper[4])
    else:
        f = f'{B}/outall/lw_{inst}.out'
        if not os.path.exists(f): problems.append((inst, 'missing')); continue
        done, sols, other, lev = parse(f)
        if len(done) != 1: problems.append((inst, 'done', done)); continue
        fl = done[0].split()
        if not (fl[3] == '0' and fl[7] == '-1' and fl[9] == '0/1' and int(fl[11]) == N): problems.append((inst, 'doneline', done[0]))
        if sols or other: problems.append((inst, 'extra', sols, other))
        for t in range(NLEV):
            if lev[t]['kt'] != kt[t] or lev[t]['ncons'] != cnt[t]: problems.append((inst, 'kt/ncons', t))
            if t + 1 < NLEV and lev[t]['kids'] != lev[t + 1]['nodes']: problems.append((inst, 'kids!=nodes', t))
        summary[inst] = dict(files=1, nodes_unique=sum(lev[t]['nodes'] for t in range(NLEV)), leaf=lev[NLEV - 1]['kids'])
extra_files = set(os.listdir(f'{B}/outall')) - {f'lw_{i}.out' for i in insts if i not in splitset} - {'ALLDONE'}
print('extra files in outall:', extra_files)
print('problems:', len(problems))
for p in problems[:50]: print('  ', p)
tot_u = sum(v['nodes_unique'] for v in summary.values()); tot_l = sum(v.get('nodes_lwsum', v['nodes_unique']) for v in summary.values())
print('instances', len(summary), 'files', sum(v['files'] for v in summary.values()), 'nodes unique %.6e lwsum-style %.6e' % (tot_u, tot_l))
print('leaf kids (level NLEV-1 children = solutions) total', sum(v['leaf'] for v in summary.values()))
for k in sorted(summary, key=lambda k: -summary[k]['nodes_unique'])[:9]: print(k, summary[k])
