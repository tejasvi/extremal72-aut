"""Coverage check for the gtestS production (audit criteria F1).
hostB run 1: dir B14 with res0..res299 (NS=300, START=0): every slice needs a progress line with done >= 12000
  (all i < 3,600,000 with i % 300 = s) and last >= 3,600,000 (or FINISHED); hostF/hostG: dir X with res0..res739
  (NS=740, START=3,600,000): every slice needs FINISHED with done = #{i in [3600000, 13485815] : i % 740 = s}.
No SOLUTION / BADLINE / other lines anywhere.  Usage: covcheck.py B14dir Xdir"""
import sys, os, re
N, M = 13485816, 3600000
hostB, xd = sys.argv[1], sys.argv[2]
bad = []; nother = 0; nsol = 0
prog = re.compile(r'^progress slice (\d+): done (\d+) last (\d+) avg ([0-9.]+)s sols (\d+)$')
fin = re.compile(r'^FINISHED slice (\d+): done (\d+) avg ([0-9.]+)s total solutions (\d+)$')
def scan(path):
    global nother, nsol
    last_prog = None; finished = None; lines = 0
    for line in open(path):
        line = line.rstrip('\n'); lines += 1
        m = prog.match(line)
        if m: last_prog = tuple(int(x) if i != 3 else float(x) for i, x in enumerate(m.groups())); 
        elif fin.match(line): finished = tuple(int(x) if i != 2 else float(x) for i, x in enumerate(fin.match(line).groups()))
        else: nother += 1; bad.append((path, line[:120]))
        if 'SOLUTION' in line: nsol += 1
    return last_prog, finished
# hostB
covered14 = 0; ok14 = 0
for s in range(300):
    p = os.path.join(hostB, f'res{s}.txt')
    if not os.path.exists(p): bad.append((p, 'MISSING')); continue
    lp, fi = scan(p)
    done = max(lp[1] if lp else 0, fi[1] if fi else 0)
    last = lp[2] if lp else -1
    if lp and lp[0] != s: bad.append((p, 'slice id mismatch'))
    if (lp and lp[4] != 0) or (fi and fi[3] != 0): bad.append((p, 'nonzero solutions'))
    if done >= 12000 and (last >= M or fi): ok14 += 1
    else: bad.append((p, f'hostB slice {s}: done {done} last {last}'))
# c72
okx = 0; totx = 0
for s in range(740):
    exp = sum(1 for _ in range(0))  # placeholder
    first = M + ((s - M) % 740)
    exp = 0 if first >= N else (N - 1 - first) // 740 + 1
    p = os.path.join(xd, f'res{s}.txt')
    if not os.path.exists(p): bad.append((p, 'MISSING')); continue
    lp, fi = scan(p)
    if fi is None: bad.append((p, f'c72 slice {s}: no FINISHED (last progress {lp})')); continue
    if fi[0] != s: bad.append((p, 'slice id mismatch'))
    if fi[3] != 0: bad.append((p, 'nonzero solutions'))
    if fi[1] == exp: okx += 1; totx += fi[1]
    else: bad.append((p, f'c72 slice {s}: done {fi[1]} expected {exp}'))
print(f"hostB slices OK: {ok14}/300 (covers indices 0..{M-1}: {M} classes)")
print(f"c72 slices OK: {okx}/740, classes decided {totx} (expected {N - M})")
print(f"union: {M + totx} of {N} classes; SOLUTION lines: {nsol}; other lines: {nother}")
for b in bad[:20]: print("PROBLEM:", b)
print("COVERAGE COMPLETE" if (ok14 == 300 and okx == 740 and totx == N - M and nsol == 0 and nother == 0) else "COVERAGE NOT (YET) COMPLETE")
