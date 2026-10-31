"""(box) flagsearch3 = flagsearch.py with the CORRECTED checkability model (keycheck.py KCSHIFT=1, 2026-10-21) and separate state per seed (fs3/y{CI}_{SEED}). Large-neighbourhood hill climb over flags for one code, scored by the checkability-key model estimate
(keycheck.py on a 50000-probe raw profile).  Move: keep the first k vectors of the current best flag (k = 1..8),
continue with flagbeam4 (objective MAXL or total-nodes, beam in {300,500,1000,2000,3000}).  Accept if the model
estimate improves.  Resumable: state in <HOME>/struct/fs/y{CI}/state.txt; every evaluated flag logged.
Usage: flagsearch.py CI START_FLAGFILE STEPS SEED"""
import sys, os, random, subprocess, re, shutil
ci = int(sys.argv[1]); start = sys.argv[2]; steps = int(sys.argv[3]); seed = int(sys.argv[4])
B = os.path.expanduser('<HOME>/struct'); W = f'{B}/fs3/y{ci}_{seed}'; os.makedirs(W, exist_ok=True)
env = dict(os.environ, TMPDIR=f'{B}/tmp')
rng = random.Random(seed)
def evaluate(flagfile, tag):
    out = f'{W}/{tag}'
    if not os.path.exists(out + '_key.txt'):
        subprocess.run([f'{B}/boxsrc/scan_box.sh', str(ci), f'fs3_{seed}_{tag}', flagfile, '50000'], env=env, check=False)
        src = f'{B}/scan/y{ci}_fs3_{seed}_{tag}_key.txt'
        if not os.path.exists(src): return None, None
        shutil.copy(src, out + '_key.txt')
    t = open(out + '_key.txt').read()
    m = re.search(r'raw total ([\d.e+]+)', t); e = re.search(r'  est ([\d.e+]+)', t)
    if not (m and e): return None, None
    return float(e.group(1)), float(m.group(1))
st = f'{W}/state.txt'
if os.path.exists(st):
    best_flag, best_est, best_raw, step0 = open(st).read().split('\n')[:4]; best_est = float(best_est); best_raw = float(best_raw); step0 = int(step0)
else:
    shutil.copy(start, f'{W}/start.flag'); best_flag = f'{W}/start.flag'
    best_est, best_raw = evaluate(best_flag, 'start'); step0 = 0
    open(st, 'w').write(f'{best_flag}\n{best_est}\n{best_raw}\n0\n')
log = open(f'{W}/log.txt', 'a')
for s in range(step0, steps):
    words = open(best_flag).read().split()[1:]
    k = rng.randint(1, 10); obj = rng.choice(['m', 'l']); beam = rng.choice([300, 500, 1000, 2000, 3000, 5000, 8000])
    tag = f's{s}_k{k}{obj}{beam}'; nf = f'{W}/{tag}.flag'
    e = dict(env); e['MAXL'] = '1' if obj == 'm' else ''
    if obj == 'l': e.pop('MAXL', None)
    r = subprocess.run(['nice', '-n', '10', f'{B}/src/flagbeam4', f'{B}/inst/data/gen_{ci}.txt', f'{B}/inst/data/low_{ci}.txt', str(beam), ','.join(words[:k])],
                       env=e, capture_output=True, text=True)
    fl = [l for l in r.stdout.split('\n') if l.startswith('FLAG')]
    if not fl: continue
    open(nf, 'w').write(fl[0] + '\n')
    est, raw = evaluate(nf, tag)
    acc = est is not None and est < best_est
    log.write(f'{s} {tag} est {est} raw {raw} best_est {best_est} {"ACCEPT" if acc else ""}\n'); log.flush()
    if acc: best_flag, best_est, best_raw = nf, est, raw
    open(st, 'w').write(f'{best_flag}\n{best_est}\n{best_raw}\n{s + 1}\n')
print(f'Y{ci} done: best {best_flag} est {best_est:.3e} raw {best_raw:.3e}')
