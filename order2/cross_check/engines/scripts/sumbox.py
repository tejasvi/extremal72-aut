"""Summarise the box differential-test logs (audit code).  The first engine of each comparison line is its reference
(lwe8, or lwe10b for runs with the bit-granular LTS file).  --partial also counts the comparison lines of logs without
a SUMMARY line (tasks stopped at the end of a box grant; every comparison line is complete on its own).
Usage: sumbox.py [--partial] LOGDIR [LOGDIR ...]"""
import sys, os, glob, re, ast, collections

tot = collections.Counter(); per_eng = collections.Counter(); per_eng_bad = collections.Counter()
pkgs = set(); kinds = collections.Counter(); nodes = 0; sols = 0; core = collections.Counter(); incomplete = []
refnodes = collections.Counter(); refsols = collections.Counter(); refruns = collections.Counter()
partial = '--partial' in sys.argv; npartial = 0
for d in [x for x in sys.argv[1:] if x != '--partial']:
    for f in sorted(glob.glob(os.path.join(d, '*.log'))):
        txt = open(f).read().split('\n')
        summ = [l for l in txt if l.startswith('SUMMARY')]
        if not summ:
            incomplete.append(os.path.basename(f))
            if not partial: continue
            npartial += 1; s = ''
        else: s = summ[-1]
        if '{' in s:                                  # core_test (lwe8 without symmetry vs naive)
            dct = ast.literal_eval(s[s.index('{'):])
            core.update(dct); core['logs'] += 1
            pkgs.add(s.split()[1].split('_')[0]); continue
        for l in txt:
            if not (l.startswith('OK ') or l.startswith('MISMATCH ')): continue
            ok = l.startswith('OK ')
            tot['lines'] += 1; tot['ok' if ok else 'MISMATCH'] += 1
            if 'SPLITSUM' in l: tot['splitsum'] += 1; continue
            tag = l.split()[1]; pkgs.add(tag.split('_')[0].replace('L', '_L').split('_')[0])
            kind = 'part' if ' part ' in l and ' pin ' not in l else ('pin-part' if ' part ' in l else 'pin')
            kinds[kind] += 1
            res = re.findall(r'(\w+)=(same|DIFF|TIMEOUT)', l)
            ref = res[0][0]                           # the first engine of a line is its reference
            for e, r in res[1:]:
                k = e if ref == 'lwe8' else e + '@' + ref
                per_eng[k] += 1
                if r != 'same': per_eng_bad[k] += 1
            m = re.search(r'nodes=(\d+) sols=(\d+)', l)
            if m:
                if ref == 'lwe8': nodes += int(m.group(1)); sols += int(m.group(2))
                else: refnodes[ref] += int(m.group(1)); refsols[ref] += int(m.group(2)); refruns[ref] += 1
print('comparison lines', dict(tot))
print('kinds (runs compared, all engines on the same input)', dict(kinds))
print('per engine vs lwe8 (engine@ref: vs that reference): compared', dict(per_eng), 'not identical', dict(per_eng_bad))
print(f'lwe8 nodes in compared runs {nodes:.4e}; SOLUTION lines compared {sols}')
for r in sorted(refruns): print(f'reference {r}: runs {refruns[r]}, nodes {refnodes[r]:.4e}, SOLUTION lines {refsols[r]}')
print('packages', len(pkgs), sorted(pkgs))
print('lwe8 (no symmetry) vs naive engine:', dict(core))
print('incomplete logs (no SUMMARY):', incomplete, '(their comparison lines counted)' if partial else '(not counted)')
