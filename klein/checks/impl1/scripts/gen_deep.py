"""Deep assignments: naive random descents reaching level L, each completed with NC random completions of the
variables of levels >= L.  Writes one hex assignment per line.  Usage: gen_deep.py INSTANCE L NPREF NCOMP SEED OUT"""
import sys, subprocess, random, os
HERE = os.path.dirname(os.path.abspath(__file__))
S = HERE + '/../scripts'
inst, L, npf, ncomp, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
with open(inst) as f: N = int(f.readline().split()[0]); vs = list(map(int, f.readline().split()))
o = subprocess.run([f'{S}/naive', inst, 'probe', str(L), str(seed), str(npf)], capture_output=True, text=True).stdout
pre = [(int(l.split()[1], 16) << 64) | int(l.split()[2], 16) for l in o.split('\n') if l.startswith('PREFIX')]
rnd = random.Random(seed)
with open(out, 'w') as f:
    for x in pre:
        for _ in range(ncomp): f.write(f'{x | (rnd.getrandbits(N - vs[L]) << vs[L]):x}\n')
print(o.strip().split('\n')[-1], 'written', len(pre) * ncomp)
