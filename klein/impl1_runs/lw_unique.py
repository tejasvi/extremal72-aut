"""Unique node counts of the level-wise engine (Implementation I) runs from the archived outputs.
Split jobs recompute levels <= SPL; level-SPL nodes are counted in every job. Unique per instance =
sum_{t<=SPL} nodes (one job; checked identical) + sum over jobs of sum_{t>SPL} nodes."""
import os, re, glob, sys, collections
base = sys.argv[1]
files = [f for d in ('out', 'outall', 'out35') for f in glob.glob(os.path.join(base, d, 'lw_*.out'))]
by = collections.defaultdict(list)
for f in files:
    txt = open(f).read().split('\n')
    m = re.match(r'DONE lwe nsol (\d+) time (\d+)s split (-?\d+) part (\d+)/(\d+) N (\d+)', txt[0])
    assert m, f
    lv = {}
    for l in txt[1:]:
        mm = re.match(r'LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+) kids (\d+)', l)
        if mm: lv[int(mm.group(1))] = int(mm.group(2))
    inst = re.match(r'lw_(\d+_\d+)(_\d+)?\.out', os.path.basename(f)).group(1)
    by[inst].append(dict(nsol=int(m.group(1)), cpu=int(m.group(2)), spl=int(m.group(3)), part=int(m.group(4)), npart=int(m.group(5)), N=int(m.group(6)), lv=lv))
print('files', len(files), 'instances', len(by))
tot_sum = tot_u = cpu = nsol = 0; mism = 0; res = {}
for inst, parts in by.items():
    spl = parts[0]['spl']; npart = parts[0]['npart']
    assert len(parts) == npart and sorted(p['part'] for p in parts) == list(range(npart)), inst
    s = sum(sum(p['lv'].values()) for p in parts)
    if spl < 0:
        u = s
    else:
        up = {t: c for t, c in parts[0]['lv'].items() if t <= spl}
        for p in parts:
            if {t: c for t, c in p['lv'].items() if t <= spl} != up: mism += 1
        u = sum(up.values()) + sum(c for p in parts for t, c in p['lv'].items() if t > spl)
    res[inst] = (s, u, spl, npart)
    tot_sum += s; tot_u += u; cpu += sum(p['cpu'] for p in parts); nsol += sum(p['nsol'] for p in parts)
print('sum over jobs (as totals.txt):', tot_sum, '%.6e' % tot_sum)
print('unique:', tot_u, '%.6e' % tot_u, ' cpu-s:', cpu, ' solutions:', nsol, ' upper-level mismatches:', mism)
for inst, (s, u, spl, npart) in sorted(res.items(), key=lambda kv: -kv[1][1])[:8]:
    print(f'  {inst}: split {spl} x {npart}: summed {s}, unique {u}')
