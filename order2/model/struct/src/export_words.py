"""Export the constraint system of an instance for wchain.c: header 'N NW', then per word:
'wt L m y' and m hex forms (the forms span the syndrome functionals; constants are irrelevant for spans).
Also prints the flag's heuristic profile: per level t, F_t = vstart[t], L_t = sum of -log2 p over constraints
with lv < t, log2N_t = F_t - L_t, and lse total."""
import sys, math
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *
I = read_inst(sys.argv[1]); out = sys.argv[2]
cons = I['cons']; vs = I['vstart']
lines = [f"{I['N']} {len(cons)}"]
for c in cons:
    p = pass_prob(c)[0]; c['L'] = -math.log2(p)
    lines.append(f"{c['wt']} {c['L']:.9f} {len(c['forms'])} {c.get('y', 0)}")
    lines.append(' '.join(f"{f:x}" for f in c['forms']))
open(out, 'w').write('\n'.join(lines) + '\n')
tot = 0; prof = []
for t in range(1, I['NLEV'] + 1):
    L = sum(c['L'] for c in cons if c['lv'] < t)
    ln = vs[t] - L; prof.append(ln); tot += 2 ** ln
print('flag profile log2N per level:', ' '.join(f"{x:.1f}" for x in prof))
print(f"flag heuristic: peak {max(prof):.2f} total log2 {math.log2(tot):.2f}")
