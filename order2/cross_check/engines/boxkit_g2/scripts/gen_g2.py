"""tasks2b.txt for the hostM wave 2: the tasks of tasks2.txt not yet started (log or prefix file exists), pins first, then
the part tasks in rounds (round k = part task k of every package).  Audit code.  Usage: gen_g2.py KIT"""
import sys, os, re
kit = sys.argv[1]
lines = [l.split() for l in open(os.path.join(kit, 'tasks2.txt')) if l.strip()]
tag = lambda l: l[5] if l[0] == 'part' else (l[8] if l[0] in ('pin', 'pinns') else l[6])
started = lambda t: os.path.exists(os.path.join(kit, 'logs', t + '.log')) or os.path.exists(os.path.join(kit, 'work', t + '.pfx'))
todo = [l for l in lines if not started(tag(l))]
pins = [l for l in todo if l[0] != 'part']
parts = sorted([l for l in todo if l[0] == 'part'], key=lambda l: (int(re.search(r'(\d+)$', tag(l)).group(1)), l[1]))
with open(os.path.join(kit, 'tasks2b.txt'), 'w') as f:
    for l in pins + parts: f.write(' '.join(l) + '\n')
print('pins', len(pins), 'parts', len(parts), 'skipped (started)', len(lines) - len(todo))
