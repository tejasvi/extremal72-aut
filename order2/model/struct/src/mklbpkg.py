"""Make a proper rc11 package (explore runs2 layout + the LTSB convention of alg/coverage-check) from a package's lb/ inputs.
runs/NEW/: flag.txt key.txt (from runs/SRC), inst.txt inst.txt.meta sym.ltsh sym.ltsb (from runs/SRC/lb), tools/ (the STRUCT
tools that built lb/: greedy basis, rebasis, LTSH, LTSB), BUILD.txt, samples/ (the exact lwe10b parts of lb/samples_b),
INPUTS.sha256 (every input file incl. sym.ltsb and tools/, plus the frozen/ lines of SRC), PLAN.txt with the line
'LTSBFILE sym.ltsb' and PROBE_LTS including the bit-granular test.
Usage: mklbpkg.py SRC NEW SPLIT_LEVEL NPART PROBE_LTS_WITH_LTSB PROBE_RAW CODE_DESCRIPTION"""
import sys, os, shutil, hashlib, glob, re, statistics as st
B = '<HOME>/c72/c2opt/struct'
src, new, spl, npart, probe, praw, desc = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6], sys.argv[7]
S, N = f'{B}/runs/{src}', f'{B}/runs/{new}'
assert not os.path.exists(N), f'{N} exists: packages are immutable, use a new name'
os.makedirs(f'{N}/tools'); os.makedirs(f'{N}/samples')
for f in ('flag.txt', 'key.txt'): shutil.copy(f'{S}/{f}', f'{N}/{f}')
for f in ('inst.txt', 'inst.txt.meta', 'sym.ltsh', 'sym.ltsb', 'BUILD.txt'): shutil.copy(f'{S}/lb/{f}', f'{N}/{f}')
for f in ('partsim2.py', 'rebasis.py', 'mkkey.py', 'mkltsb.py', 'ltsblib.py', 'partbits_lib.py', 'instio.py', 'keyh0.py', 'lwe10b.c', 'mklb.sh'):
    shutil.copy(f'{B}/src/{f}', f'{N}/tools/{f}')
logs = sorted(glob.glob(f'{S}/lb/samples_b/*.log'))
for f in logs: shutil.copy(f, f'{N}/samples/')
for f in glob.glob(f'{S}/lb/samples_b/*.time'): shutil.copy(f, f'{N}/samples/')
# estimate from the lwe10b parts
vals, users, pre, nsol = [], [], None, 0
for f in logs:
    t = open(f).read()
    if 'DONE' not in t: continue
    nsol += t.count('\nSOLUTION')
    m = re.search(r'parts? of|s(\d+)n(\d+)_p', os.path.basename(f))
    lv = {int(a): int(b) for a, b in re.findall(r'LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+)', t)}
    vals.append(sum(v for k, v in lv.items() if k > spl)); pre = sum(v for k, v in lv.items() if k <= spl)
    u = re.search(r'user ([\d.]+)', t); users.append(float(u.group(1)) if u else 0.0)
assert nsol == 0
nfn = re.search(r's(\d+)n(\d+)_p', os.path.basename(logs[0])); sspl, sn = int(nfn.group(1)), int(nfn.group(2))
assert sspl == spl
mu = st.mean(vals); se = st.stdev(vals) / len(vals) ** 0.5; tot = mu * sn + pre
key = open(f'{N}/key.txt').read().split()[1:]
def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
lines = []
for f in ['flag.txt', 'key.txt', 'inst.txt', 'inst.txt.meta', 'sym.ltsh', 'sym.ltsb', 'BUILD.txt'] + [f'tools/{x}' for x in sorted(os.listdir(f'{N}/tools'))]:
    lines.append(f'{sha(f"{N}/{f}")}  {f}')
lines += [l.rstrip('\n') for l in open(f'{S}/INPUTS.sha256') if ' frozen/' in l]
open(f'{N}/INPUTS.sha256', 'w').write('\n'.join(lines) + '\n')
ci = int(''.join(ch for ch in src.split('-')[0] if ch.isdigit()))
plan = [
  f"CODE {new}  (0-based index in codes36.txt: {ci}; {desc}; rc11 package: the instance of {src} with the key word's constraint rewritten in a greedy syndrome basis, its LTSH, and the bit-granular LTS file sym.ltsb; raw counts identical to {src})",
  f"SPLIT_LEVEL {spl}",
  f"NPART {npart}",
  "LTSBFILE sym.ltsb",
  f"PROBE_LTS {probe}   (PROBES=20000 with LTSHFILE=sym.ltsh LTSBFILE=sym.ltsb; lwe10b and rc11 give identical probes)",
  f"PROBE_RAW {praw}",
  f"SAMPLE_EST_NODES {tot:.3e}   ({len(vals)} seeded parts of 1/{sn} at split {spl}, struct lwe10b with LTSBFILE on hostM (rc11 is byte-identical to lwe10b per alg): mean {mu:.4e} nodes per part, +-{100 * se / mu:.1f}% (1 s.e.), max/mean {max(vals) / mu:.2f}; levels > {spl}; logs samples/)",
  f"EST_CPU lwe10b prototype {st.mean(users):.0f} user-s per 1/{sn} part on hostM (<CPU>, loaded); rc11 is ~6x faster per node than lwe10b (alg)",
  f"KEYH0 |H0| = 1 (key words as in {src}: {','.join(key)})",
  f"BUILD: runs/{src} (frozen prep_code.py) -> tools/mklb.sh {src} (greedy basis tools/partsim2.py, tools/rebasis.py, tools/mkkey.py words:<key>, tools/mkltsb.py); see BUILD.txt for the basis and hashes",
  f"RUN: frozen_rc11/run_parts.sh {new} {spl} {npart} FIRST LAST NPROC (passes LTSBFILE=CODEDIR/sym.ltsb to every part)",
  f"CHECK: frozen_rc11/check_box.sh {new} (inputs incl. sym.ltsb, frozen sources, PROBE with LTSB, lwe8 vs rc11 without LTSB, lwe10b vs rc11 with LTSB)",
  "VALIDATION: bit-granular LTS QR48 controls (struct/src/qr48keyb.py: 20 configurations, closure 5760, 0 outside); alg: rc11/lwe11b5 byte-identical to lwe10b incl. LBPRUNE on the tier C parts (48/48) and 40 parts of the runs_lb instances",
]
open(f'{N}/PLAN.txt', 'w').write('\n'.join(plan) + '\n')
print(f'{new}: {len(vals)} parts, est {tot:.3e}, INPUTS {sha(N + "/INPUTS.sha256")[:16]}')
