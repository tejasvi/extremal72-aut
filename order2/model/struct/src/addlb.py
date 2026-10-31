"""Append the bit-granular / greedy-basis variant estimates to a package's PLAN.txt (from runs/NAME/lb/samples_{b,p}).
Usage: addlb.py NAME SPL NPART PROBE_LB"""
import sys, glob, re, statistics as st
B = '<HOME>/c72/c2opt/struct/runs'
n, spl, npart, probe = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
def est(m):
    vals, users, pre = [], [], None
    for f in sorted(glob.glob(f'{B}/{n}/lb/samples_{m}/*.log')):
        t = open(f).read()
        if 'DONE' not in t: continue
        lv = {int(a): int(b) for a, b in re.findall(r'LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+)', t)}
        vals.append(sum(v for k, v in lv.items() if k > spl)); pre = sum(v for k, v in lv.items() if k <= spl)
        u = re.search(r'user ([\d.]+)', t); users.append(float(u.group(1)) if u else 0.0)
    if len(vals) < 2: return None
    mu = st.mean(vals); se = st.stdev(vals) / len(vals) ** 0.5
    return len(vals), mu * npart + pre, 100 * se / mu, max(vals) / mu, st.mean(users)
L = open(f'{B}/{n}/PLAN.txt').read().rstrip('\n').split('\n')
L = [l for l in L if not l.startswith('LB_')]
r = est('p')
if r:
  k, e, s, mm, u = r
  L.append(f"LB_RC9 greedy-basis variant for the plain engine: lb/inst.txt + LTSHFILE=lb/sym.ltsh (same flag and key words; key-word constraint rewritten in the greedy basis, raw counts identical; lb/BUILD.txt): SAMPLE_EST_NODES {e:.3e} ({k} parts of 1/{npart} at split {spl}, frozen3/lwe10 on hostM, +-{s:.1f}%, max/mean {mm:.2f}, {u:.0f} user-s per part; logs lb/samples_p)")
r = est('b')
if r:
  k, e, s, mm, u = r
  L.append(f"LB_RC11 the same plus the bit-granular LTS test, LTSBFILE=lb/sym.ltsb (prototype struct/src/lwe10b.c; production rc11): SAMPLE_EST_NODES {e:.3e} ({k} parts, +-{s:.1f}%, max/mean {mm:.2f}, {u:.0f} user-s per part; logs lb/samples_b)")
L.append(f"LB_PROBE_LTS {probe} (frozen3/lwe10, PROBES=20000, lb/inst.txt with lb/sym.ltsh, no LTSB)")
open(f'{B}/{n}/PLAN.txt', 'w').write('\n'.join(L) + '\n')
print('\n'.join(L[-3:]))
