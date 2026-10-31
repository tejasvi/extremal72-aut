# LHS of the weighted double count from OWN values: cert3 histogram (scan/full_*.hist V lines) + autnd (ND codes)
from fractions import Fraction
import glob, re
S = '../scan/'
lhs = Fraction(0); mass = Fraction(0); ncls = 0; nmon = 0; nsc1 = 0
for fn in sorted(glob.glob(S + 'full_*.hist')):
    for l in open(fn):
        if l.startswith('V '):
            _, a8, aut, sc, cnt = l.split(); a8, aut, sc, cnt = int(a8), int(aut), int(sc), int(cnt)
            w = 1 if sc else 2
            lhs += Fraction(w * cnt * (a8 // 3), aut); mass += Fraction(w * cnt * 3, aut)
            ncls += cnt; nmon += w * cnt; nsc1 += cnt if sc else 0
# ND codes: A8 from the cls24 line (equal to own A8 for every line, see scan), aut/sc own (autnd)
a8_of = {}
for l in open(S + 'nd_all.txt'):
    idx = int(l.split()[0]); code = l.split('| ')[1].split()
    a8_of[idx] = int(code[2])
bad = 0; nd = 0
for fn in sorted(glob.glob(S + 'nd_part_0*.aut')):
    for l in open(fn):
        f = l.split(); idx = int(f[0])
        d = dict(x.split('=') for x in f[1:] if '=' in x)
        if 'MISMATCH' in l: bad += 1
        aut = int(d['my_aut']); sc = int(d['my_sc']); w = 1 if sc else 2
        lhs += Fraction(w * (a8_of[idx] // 3), aut); mass += Fraction(w * 3, aut)
        ncls += 1; nmon += w; nsc1 += sc; nd += 1
print('classes', ncls, 'Mon classes', nmon, 'self-conjugate', nsc1, 'ND processed', nd, 'of', len(a8_of), 'mismatches', bad)
print('LHS = sum (A8/3)/|Aut| =', lhs, '=', float(lhs))
print('target 526493209678523/322560 :', lhs == Fraction(526493209678523, 322560))
print('mass sum_Mon 3/|Aut| =', float(mass))
