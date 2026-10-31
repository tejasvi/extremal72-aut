"""Own coverage check of the gtestS production (audit).
usage: cov_gt.py hostB_DIR C72_DIR   (directories holding res{s}.txt copies)
hostB: slices s=0..299 of NS=300 from 0; each must have a progress line with last >= M (or FINISHED covering it).
hostF/hostG: slices s=0..739 of NS=740 from M=3600000; each must have FINISHED with done = expected(s).
Every progress line is checked for consistency (last = s mod NS, done = position of last in the slice), sols = 0;
no SOLUTION, BADLINE or other lines anywhere."""
import sys, os, re
N, M = 13485816, 3600000
pro = re.compile(r'^progress slice (\d+): done (\d+) last (\d+) avg (\S+)s sols (\d+)$')
fin = re.compile(r'^FINISHED slice (\d+): done (\d+) avg (\S+)s total solutions (\d+)$')
def scan(path, s, NS, start):
    issues = []; maxlast = -1; finished = None; nprog = 0
    first = start + ((s - start) % NS)          # smallest i >= start with i = s mod NS
    for line in open(path, errors='replace'):
        line = line.rstrip('\n')
        if not line: continue
        m = pro.match(line)
        if m:
            nprog += 1
            ss, d, last, sols = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(5))
            if ss != s: issues.append('slice id %d in file of slice %d' % (ss, s))
            if last % NS != s % NS: issues.append('last %d not = s mod NS' % last)
            if d != (last - first) // NS + 1: issues.append('done %d inconsistent with last %d' % (d, last))
            if sols: issues.append('sols %d' % sols)
            maxlast = max(maxlast, last); continue
        m = fin.match(line)
        if m:
            finished = (int(m.group(1)), int(m.group(2)), int(m.group(4))); continue
        issues.append('OTHER: ' + line[:200])
    return maxlast, finished, nprog, issues, first
ok = True
hostB, c72 = sys.argv[1], sys.argv[2]
bad14 = 0
for s in range(300):
    p = os.path.join(hostB, 'res%d.txt' % s)
    if not os.path.exists(p): print('hostB slice', s, 'MISSING FILE'); ok = False; bad14 += 1; continue
    maxlast, fin_, nprog, issues, first = scan(p, s, 300, 0)
    covered = maxlast >= M or (fin_ is not None and fin_[1] == len(range(first, N, 300)))
    if not covered or issues or (fin_ and fin_[2]):
        ok = False; bad14 += 1; print('hostB slice', s, 'maxlast', maxlast, 'fin', fin_, 'issues', issues[:3])
print('hostB: slices with problems', bad14)
badc = 0; tot = 0
for s in range(740):
    p = os.path.join(c72, 'res%d.txt' % s)
    if not os.path.exists(p): print('c72 slice', s, 'MISSING FILE'); ok = False; badc += 1; continue
    maxlast, fin_, nprog, issues, first = scan(p, s, 740, M)
    exp = len(range(first, N, 740))
    if fin_ is None or fin_[1] != exp or fin_[2] != 0 or issues or fin_[0] != s:
        ok = False; badc += 1; print('c72 slice', s, 'fin', fin_, 'expected', exp, 'issues', issues[:3])
    else: tot += exp
print('c72: slices with problems', badc, 'codes covered by FINISHED slices', tot, 'expected', N - M)
print('VERDICT', 'PASS' if ok and tot == N - M else 'CHECK')
