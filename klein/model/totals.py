"""Exact totals of the C2xC2 runs: lwe (impl1_runs/out, outall, out35) and the GD solver (gd_runs/out, out2, test).
Paths are relative to the klein directory (the parent of this script's directory)."""
import glob, os, re
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
def lwe_parse(f):
    t = open(f).read()
    d = [l for l in t.split('\n') if l.startswith('DONE lwe')]
    if len(d) != 1: return None
    fl = d[0].split()
    nodes = sum(int(l.split()[7]) for l in t.split('\n') if l.startswith('LEVEL'))
    return int(fl[3]), int(fl[5].rstrip('s')), nodes
print("== level-wise engine (lwe)")
tot = [0, 0, 0, 0]
per = {}
for pat in ('impl1_runs/out/lw_*.out', 'impl1_runs/outall/lw_*.out', 'impl1_runs/out35/lw_*.out'):
    for f in glob.glob(pat):
        r = lwe_parse(f)
        assert r is not None, f
        m = re.match(r'.*lw_(\d+_\d+)(_\d+)?\.out', f); inst = m.group(1)
        a = per.setdefault(inst, [0, 0, 0, 0]); a[0] += 1; a[1] += r[0]; a[2] += r[1]; a[3] += r[2]
        tot[0] += 1; tot[1] += r[0]; tot[2] += r[1]; tot[3] += r[2]
print(f"instances {len(per)}, output files {tot[0]}, solutions {tot[1]}, cpu-s {tot[2]}, nodes {tot[3]:.6e}")
big = sorted(per.items(), key=lambda kv: -kv[1][3])[:8]
for k, v in big: print(f"  {k}: files {v[0]}, sols {v[1]}, cpu-s {v[2]}, nodes {v[3]}")
print("== guess-and-determine solver (v4gd)")
old = set()
for l in open('gd_runs/wide_status.txt'):
    t, i, p = l.split()
    if t == 'OLD': old.add((i, int(p)))
insts = sorted(set(re.sub(r'v4_(\d+_\d+)\.txt(\.gz)?', r'\1', os.path.basename(f)) for f in glob.glob('gd_runs/inst/v4_*.txt*')))
hard = {'3_6', '15_2', '20_7', '21_2', '23_2', '25_2'}
gtot = [0, 0, 0]; done_inst = 0
def gd_done(f):
    try:
        for l in open(f):
            if l.startswith('DONE result=COMPLETE'): return l
    except FileNotFoundError: return None
for i in insts:
    if i in hard: continue
    if i == '0_0':
        ls = [gd_done(f'gd_runs/test/w14_{p}.out') for p in range(64)]
    else:
        ls = [gd_done(f'gd_runs/out2/v4_{i}_{p}.out' if (i, p) in old else f'gd_runs/out/v4_{i}_{p}.out') for p in range(16)]
    if all(ls):
        done_inst += 1
        for l in ls:
            fl = l.split(); gtot[0] += int(fl[3]); gtot[1] += int(fl[5]); gtot[2] += int(fl[7].rstrip('s'))
print(f"instances complete {done_inst} (of {len(insts) - len(hard)} non-hard), nodes {gtot[0]:.6e}, sols {gtot[1]}, cpu-s {gtot[2]}")
