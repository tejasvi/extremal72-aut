"""Compare per-E_B glue counts: first program frames.c count-only (cls/c24count.*.txt: 'ebindex canonical_frames aut[x2]')
against second program rglue (full/all.eb: 'B id aut sc orbits N_phi ...'), matched by cform key."""
import glob
C = '../../classification/program1/'; X = '../../classification/program2/'
ckey = [l.split()[1] for l in open(C + 'eb/n24.L5.txt')]
xkey = [l.split()[0] for l in open(X + 'n24/L5.cfkeys.txt')]
xid = {k: j for j, k in enumerate(xkey)}
assert len(ckey) == 45775 and len(xkey) == 45775 and len(xid) == 45775
eb = {}
for l in open(X + 'full/all.eb'):
    f = l.split()
    if f[0] != 'B': continue
    eb[int(f[1])] = (int(f[2]), int(f[3]), int(f[4]), int(f[5]))
seen = set(); nmatch = 0; mism = []
for fn in sorted(glob.glob(C + 'cls/c24count.*.txt')):
    for l in open(fn):
        f = l.split()
        if len(f) < 3: continue          # line still being written
        i, cf, a = int(f[0]), int(f[1]), f[2]
        aut = int(a.replace('x2', '')); sc = 0 if 'x2' in a else 1
        j = xid[ckey[i]]
        xa, xs, xorb, xn = eb[j]
        if i in seen: mism.append(('dup', i)); continue
        seen.add(i)
        if (cf, aut, sc) == (xorb, xa, xs) and xn == xorb * 120960: nmatch += 1
        else: mism.append((i, cf, aut, sc, j, xorb, xa, xs, xn))
print('c3class count lines', len(seen), 'of 45775; matching rglue (orbits, aut, sc, N_phi = 120960*orbits):', nmatch)
print('mismatches', len(mism), mism[:10])
