"""parse the full-run logs into a per-depth statistics table (markdown)"""
import re, sys, glob, os
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results')
files = {0: [base + '/hostA/logs/full_k0_s0.log', base + '/hostB/logs/full_k0_s1.log']}
for k in range(1, 7): files[k] = [base + '/hostA/logs/full_k%d_all.log' % k]
tot = {}
rows = []
grand_user = 0.0
for k, fl in files.items():
    acc = {}; user = 0.0; sols = 0; nl1 = None; nn1 = None; stab = None
    for f in fl:
        for line in open(f):
            m = re.match(r'\s+(\d)\s+(\d)\s+(\d+)\s+(\S+)\s+(\d+)', line)
            if m:
                d = int(m.group(1)); t = int(m.group(3)); e = 0 if m.group(4) == '-' else int(m.group(4)); n = int(m.group(5))
                a = acc.setdefault(d, [0, 0, 0])
                if d == 1: a[0] = t; a[2] += n
                else: a[0] += t; a[1] += e; a[2] += n
            m = re.search(r'USER ([\d.]+)', line)
            if m: user += float(m.group(1))
            m = re.match(r'SOLUTIONS (\d+)', line)
            if m: sols += int(m.group(1))
            m = re.search(r'\|L1\| \(mu5-classes\) = (\d+), depth-1 nodes .* = (\d+)', line)
            if m: nl1, nn1 = int(m.group(1)), int(m.group(2))
            m = re.search(r'\|Stab\(r\)\|=(\d+)', line)
            if m: stab = int(m.group(1))
    grand_user += user
    rows.append((k, nl1, nn1, stab, acc, sols, user))
    for d, a in acc.items():
        t = tot.setdefault(d, [0, 0, 0])
        for i in range(3): t[i] += a[i]
print("| K0 | stab | L1 classes | depth-1 nodes | d2 tested / colext / nodes | d3 tested / colext / nodes | d4 tested / colext / nodes | d5 nodes | d6 (solutions) | CPU s |")
print("|---|---|---|---|---|---|---|---|---|---|")
for k, nl1, nn1, stab, acc, sols, user in rows:
    f = lambda d: "%s / %s / %s" % ('{:,}'.format(acc[d][0]), '{:,}'.format(acc[d][1]), '{:,}'.format(acc[d][2]))
    print("| %d | %d | %s | %s (%s pass col.) | %s | %s | %s | %s | %d | %.0f |" % (k, stab, '{:,}'.format(nl1), '{:,}'.format(nn1), '{:,}'.format(acc[1][2]), f(2), f(3), f(4), '{:,}'.format(acc[5][2]), sols, user))
f = lambda d: "%s / %s / %s" % ('{:,}'.format(tot[d][0]), '{:,}'.format(tot[d][1]), '{:,}'.format(tot[d][2]))
print("| all | | | %s | %s | %s | %s | %s | %d | %.0f |" % ('{:,}'.format(tot[1][2]), f(2), f(3), f(4), '{:,}'.format(tot[5][2]), sum(r[5] for r in rows), grand_user))
print("total CPU (user) seconds: %.0f = %.2f vCPU-hours" % (grand_user, grand_user / 3600))
