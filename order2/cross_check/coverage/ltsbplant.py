"""Per-package verdict file for the planted LTSB tests (audit, coverage-check).  usage: ltsbplant.py PKG
Reads c3/plant/runs_lbp_PKG.log (pinned), compl_lbp_PKG.log (whole-orbit) and runs_lbm_PKG.log (mutant controls) and
writes c3/ltsbplant_PKG.txt ending in 'VERDICT PASS' or 'VERDICT FAIL'.  PASS needs:
  - pinned: every engine keeps the K-minimal member in every min instance and prunes every non-min member;
    every complete output equals the lwe10b+LTSB reference (levels=same, LBPRUNE included); no stopped or failed run
    (done=0 = a self-check stop under LWE11CHECK);
  - whole-orbit: every engine reports every K-minimal member in every instance; outputs equal the reference;
  - mutant controls: the unmutated reference passes every min instance, and each mutant (mut1: no per-bit guard,
    mut4: non-prefix compare) loses the K-minimal member at least once (the tests can detect bit-test bugs here);
  - the bit test fired (lbprune > 0) in at least one rc11 run, so the bit test was exercised."""
import sys, os, re, hashlib, time
C = '<HOME>/c72/audit/c2audit/c3'; PL = C + '/plant'
pkg = sys.argv[1]
logs = {'pinned': f'{PL}/runs_lbp_{pkg}.log', 'whole-orbit': f'{PL}/compl_lbp_{pkg}.log', 'mutants': f'{PL}/runs_lbm_{pkg}.log'}
def sha(fn):
    return hashlib.sha256(open(fn, 'rb').read()).hexdigest()
probs = []; out = []
out.append(f'LTSB planted tests for package {pkg} (coverage-check), written {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}')
P = f'<HOME>/c72/c2opt/struct/runs/{pkg}'
for f in ('inst.txt', 'sym.ltsh', 'sym.ltsb', 'key.txt'):
    out.append(f'input {f}: {sha(os.path.join(P, f)) if os.path.exists(os.path.join(P, f)) else "MISSING"}')
for name, fn in logs.items():
    if not os.path.exists(fn): probs.append(f'{name} log missing: {fn}'); continue
    out.append(f'log {name}: {fn} sha256 {sha(fn)}')
rx = re.compile(r'^\S+ s(\d+) m(\d) (?:(min|nonmin) )?(\S+) done=(\d+) stopped=(\d+) levels=(\w+)(?: lbprune=(\d+))? \| (.*)$')
def parse(fn):
    rows = []
    if not os.path.exists(fn): return rows
    for ln in open(fn):
        m = rx.match(ln.strip())
        if m: rows.append(dict(seed=int(m.group(1)), mode=int(m.group(2)), w=m.group(3), eng=m.group(4), done=int(m.group(5)),
                               stopped=int(m.group(6)), levels=m.group(7), lb=int(m.group(8) or 0), verdict=m.group(9)))
    return rows
# pinned
R = parse(logs['pinned']); lbfired = 0
engs = sorted(set(r['eng'] for r in R))
for e in engs:
    mins = [r for r in R if r['eng'] == e and r['w'] == 'min']; nons = [r for r in R if r['eng'] == e and r['w'] == 'nonmin']
    kp = sum('PASS (K-min member kept)' in r['verdict'] for r in mins); pr = sum('pruned (LTS active)' in r['verdict'] for r in nons)
    bad = [r for r in mins + nons if r['done'] != 1 or r['stopped'] != 0 or r['levels'] != 'same']
    if e.startswith(('rc11', 'rc13')): lbfired += sum(r['lb'] > 0 for r in mins + nons)
    out.append(f'pinned {e}: K-min kept {kp}/{len(mins)}, non-min pruned {pr}/{len(nons)}, not complete or not identical to the reference {len(bad)}')
    if kp != len(mins) or pr != len(nons) or bad or not mins: probs.append(f'pinned {e}: kept {kp}/{len(mins)}, pruned {pr}/{len(nons)}, bad {len(bad)}')
if not R: probs.append('no pinned rows')
# whole-orbit
W = parse(logs['whole-orbit'])
for e in sorted(set(r['eng'] for r in W)):
    rows = [r for r in W if r['eng'] == e]
    ok = sum('PASS (all K-min members kept)' in r['verdict'] for r in rows)
    bad = [r for r in rows if r['done'] != 1 or r['stopped'] != 0 or r['levels'] != 'same']
    if e.startswith(('rc11', 'rc13')): lbfired += sum(r['lb'] > 0 for r in rows)
    out.append(f'whole-orbit {e}: all K-min members kept {ok}/{len(rows)}, not complete or not identical to the reference {len(bad)}')
    if ok != len(rows) or bad or not rows: probs.append(f'whole-orbit {e}: {ok}/{len(rows)}, bad {len(bad)}')
if not W: probs.append('no whole-orbit rows')
# mutant controls
M = parse(logs['mutants'])
for e in ('lwe10b_lb', 'mut1_lb', 'mut4_lb'):
    mins = [r for r in M if r['eng'] == e and r['w'] == 'min']
    kp = sum('PASS (K-min member kept)' in r['verdict'] for r in mins); fl = sum('FAIL (K-min member lost)' in r['verdict'] for r in mins)
    out.append(f'mutant series {e}: K-min kept {kp}/{len(mins)}, lost {fl}/{len(mins)}')
    if e == 'lwe10b_lb' and (kp != len(mins) or not mins): probs.append(f'mutant series reference {e}: kept {kp}/{len(mins)}')
    if e != 'lwe10b_lb' and fl < 1: probs.append(f'mutant {e} never lost the K-min member: the tests do not detect this bug class here')
out.append(f'bit test fired (lbprune > 0) in {lbfired} rc11/rc13 runs')
if lbfired < 1: probs.append('the bit test never fired in an rc11/rc13 run')
for p in probs: out.append('PROBLEM: ' + p)
out.append('VERDICT ' + ('PASS' if not probs else 'FAIL'))
open(f'{C}/ltsbplant_{pkg}.txt', 'w').write('\n'.join(out) + '\n')
print(out[-1])
