"""tasks4b.txt for kit4: the pin tasks not yet started, then the part tasks in rounds (round k = part task k of every
package, longest expected lwe8 time first, from the fleet05 wave).  A task counts as started if its log or prefix file
exists.  Audit code.  Usage: gen4b.py KIT [OUTFILE (default tasks4b.txt)]"""
import sys, os
kit = sys.argv[1]
est = dict(y10b=471, y11b=228, y13=1243, y16b=48, y17=212, y18c=54, y2=779, y20=911, y20b=752, y21=817, y24b=117,
           y25=315, y27b=129, y28s=239, y29=609, y3=209, y30=742, y31=623, y32=1184, y33=88, y34=655, y35=1103,
           y36=887, y37=882, y38=426, y6=784, y7=723, y9=797)
lines = [l.split() for l in open(os.path.join(kit, 'tasks4.txt')) if l.strip()]
started = lambda t: os.path.exists(os.path.join(kit, 'logs', t + '.log')) or os.path.exists(os.path.join(kit, 'work', t + '.pfx'))
pins = [l for l in lines if l[0] in ('pin', 'pinns') and not started(l[-1])]
parts = [l for l in lines if l[0] == 'part' and not started(l[-1])]
parts.sort(key=lambda l: (int(l[-1].rsplit('part', 1)[1]), -est[l[1]], l[1]))
with open(os.path.join(kit, sys.argv[2] if len(sys.argv) > 2 else 'tasks4b.txt'), 'w') as f:
    for l in pins + parts: f.write(' '.join(l) + '\n')
print('pins', len(pins), 'parts', len(parts), 'skipped (started)', len(lines) - len(pins) - len(parts))
