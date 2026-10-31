"""LBPRUNE totals of the exact pinned sub-instances of a difftest pin run with --ltsb (same prefix selection as
difftest_c2.py: Random(SEED).shuffle, first NPREF), from the reference engine (audit code).
Usage: lbpin_stats.py PKG L PREFIXFILE NPREF SEED ENGINE WORKDIR"""
import sys, os, random, subprocess
pkg, L, pfile, npref, seed, eng, work = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], sys.argv[7]
S = os.path.dirname(os.path.abspath(__file__))
prefs = [l.split() for l in open(pfile) if l.startswith('PREFIX')]
random.Random(seed).shuffle(prefs)
inst = os.path.join(pkg, 'inst.txt'); os.makedirs(work, exist_ok=True)
tot = {}; nodes = 0
for _, hi, lo in prefs[:npref]:
    x0 = f'{(int(hi, 16) << 64) | int(lo, 16):x}'
    sub, subb = os.path.join(work, 'st.txt'), os.path.join(work, 'st.ltsb')
    subprocess.run([sys.executable, '-I', os.path.join(S, 'pin.py'), inst, sub, str(L), x0], check=True)
    subprocess.run([sys.executable, '-I', os.path.join(S, 'pinltsb.py'), inst, os.path.join(pkg, 'sym.ltsb'), str(L), x0, subb], check=True)
    env = dict(os.environ, LTSHFILE=os.path.join(pkg, 'sym.ltsh'), LTSBFILE=subb)
    out = subprocess.run([eng, sub], capture_output=True, text=True, env=env, timeout=120).stdout
    for l in out.split('\n'):
        if l.startswith('LBPRUNE'):
            for kv in l.split()[1:]:
                k, v = kv.split(':'); tot[int(k)] = tot.get(int(k), 0) + int(v)
        if l.startswith('LEVEL '): nodes += int(l.split()[7])
print(os.path.basename(pkg), 'L', L, 'prefixes', min(npref, len(prefs)), 'nodes', nodes, 'LBPRUNE by level', {k: v for k, v in sorted(tot.items()) if v})
