"""(box) Hill climb over flags scored by the REAL engine: LTS probe (PROBES=20000, lwe10) with the better of two keys
(best-orbit key 'h0fix:BESTWORDS' from keycheck.py, and 'early:8').  Moves as in flagsearch.py: keep the first k
vectors of the current best flag (k = 1..10), continue with flagbeam4 (MAXL or total-nodes objective, beam 300-8000).
Accept if the probe total improves by more than 3% (probe noise).  Resumable: state in <HOME>/struct/fs2/y{CI}_{SEED}/state.txt; every evaluated flag
logged.  Usage: flagsearch2.py CI START_FLAGFILE STEPS SEED"""
import sys, os, random, subprocess, re, shutil
ci = int(sys.argv[1]); start = sys.argv[2]; steps = int(sys.argv[3]); seed = int(sys.argv[4])
B = os.path.expanduser('<HOME>/struct'); W = f'{B}/fs2/y{ci}_{seed}'; os.makedirs(W, exist_ok=True)
T = f'{B}/tmp/fs2_y{ci}_{seed}'; os.makedirs(T, exist_ok=True)
env = dict(os.environ, TMPDIR=f'{B}/tmp')
rng = random.Random(seed)
PY = [os.path.expanduser('<HOME>/venv/bin/python'), '-I']


def total(out):
    m = re.search(r'TOTAL nodes ~ ([\d.e+]+)', out)
    return float(m.group(1)) if m else None


def evaluate(flagfile, tag):
    res = f'{W}/{tag}.res'
    if os.path.exists(res):
        v = open(res).read().split()
        return (float(v[0]), v[1]) if v and v[0] != 'None' else (None, None)
    inst = f'{T}/inst.txt'
    shutil.copy(flagfile, f'{T}/flag.txt')
    if subprocess.run([f'{B}/src/mkinst_c', f'{B}/inst/gen{ci}.txt', f'{T}/flag.txt', inst], env=env, capture_output=True).returncode:
        open(res, 'w').write('None x\n'); return None, None
    raw = subprocess.run(['nice', '-n', '10', f'{B}/runs/frozen3/lwe10', inst], env=dict(env, PROBES='20000'), capture_output=True, text=True).stdout
    open(f'{T}/raw.log', 'w').write(raw)
    kc = subprocess.run(['nice', '-n', '10'] + PY + [f'{B}/src/keycheck.py', str(ci), inst, f'{T}/raw.log'], env=env, capture_output=True, text=True).stdout
    m = re.search(r'BESTWORDS ([\d,]+)', kc)
    best = (None, None)
    specs = ['early:8'] + ([f"h0fix:{','.join(m.group(1).split(',')[:8])}"] if m else [])
    for sp in specs:
        lt = f'{T}/k.ltsh'
        r = subprocess.run(['nice', '-n', '10'] + PY + [f'{B}/src/mkkey.py', str(ci), inst, f'{T}/flag.txt', lt, sp], env=env, capture_output=True, text=True)
        if r.returncode or not os.path.exists(lt): continue
        v = total(subprocess.run(['nice', '-n', '10', f'{B}/runs/frozen3/lwe10', inst], env=dict(env, PROBES='20000', LTSHFILE=lt), capture_output=True, text=True).stdout)
        if v is not None and (best[0] is None or v < best[0]): best = (v, sp.split(':')[0])
        os.remove(lt)
    for f in (inst, inst + '.meta', inst + '.pkl'):
        if os.path.exists(f): os.remove(f)
    open(res, 'w').write(f'{best[0]} {best[1]}\n')
    return best


st = f'{W}/state.txt'
if os.path.exists(st):
    best_flag, best_val, step0 = open(st).read().split('\n')[:3]; best_val = float(best_val); step0 = int(step0)
else:
    shutil.copy(start, f'{W}/start.flag'); best_flag = f'{W}/start.flag'
    best_val, _ = evaluate(best_flag, 'start'); step0 = 0
    open(st, 'w').write(f'{best_flag}\n{best_val}\n0\n')
log = open(f'{W}/log.txt', 'a')
for s in range(step0, steps):
    words = open(best_flag).read().split()[1:]
    k = rng.randint(1, 10); obj = rng.choice(['m', 'l']); beam = rng.choice([300, 500, 1000, 2000, 3000, 5000, 8000])
    tag = f's{s}_k{k}{obj}{beam}'; nf = f'{W}/{tag}.flag'
    e = dict(env)
    if obj == 'm': e['MAXL'] = '1'
    else: e.pop('MAXL', None)
    r = subprocess.run(['nice', '-n', '10', f'{B}/src/flagbeam4', f'{B}/inst/data/gen_{ci}.txt', f'{B}/inst/data/low_{ci}.txt', str(beam), ','.join(words[:k])],
                       env=e, capture_output=True, text=True)
    fl = [l for l in r.stdout.split('\n') if l.startswith('FLAG')]
    if not fl: continue
    open(nf, 'w').write(fl[0] + '\n')
    val, kk = evaluate(nf, tag)
    acc = val is not None and val < 0.97 * best_val      # 3% margin against probe noise
    log.write(f'{s} {tag} probe {val} key {kk} best {best_val} {"ACCEPT" if acc else ""}\n'); log.flush()
    if acc: best_flag, best_val = nf, val
    open(st, 'w').write(f'{best_flag}\n{best_val}\n{s + 1}\n')
print(f'Y{ci} seed {seed} done: best {best_flag} probe {best_val:.3e}')
