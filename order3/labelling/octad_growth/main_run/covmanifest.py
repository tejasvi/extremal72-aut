"""Per-id coverage proof for the gtestS production.
Rule: id i < 3,600,000 is decided by hostB run-1 slice i % 300 (NS=300, START=0); id i >= 3,600,000 by c72 slice
i % 740 (NS=740, START=3,600,000). A hostB slice processes its residue class in increasing order; its decided ids
are all ids = s mod 300 up to its last reported index ('last' in progress lines). A c72 slice must print FINISHED with
done = size of its residue class in [3.6M, N). Checks: every id 0..N-1 assigned exactly once under the rule, every
assigned id decided, raw coverage (incl. hostB overlap past 3.6M) >= 1, no SOLUTION or other lines.
Usage: covmanifest.py hostBdir xdir"""
import sys, os, re
import numpy as np
N, M = 13485816, 3600000
hostB, xd = sys.argv[1], sys.argv[2]
prog = re.compile(r'^progress slice (\d+): done (\d+) last (\d+) avg ([0-9.]+)s sols (\d+)$')
fin = re.compile(r'^FINISHED slice (\d+): done (\d+) avg ([0-9.]+)s total solutions (\d+)$')
assigned = np.zeros(N, dtype=np.uint8)    # times decided under the rule
raw = np.zeros(N, dtype=np.uint8)         # times decided by any slice
other = 0; sols = 0; problems = []
for s in range(300):
    last = -1; done = 0; fin_seen = False
    for line in open(os.path.join(hostB, f'res{s}.txt')):
        line = line.rstrip('\n'); m = prog.match(line); f = fin.match(line)
        if m:
            if int(m.group(1)) != s: problems.append(f'hostB res{s}: slice id {m.group(1)}')
            done, last = int(m.group(2)), int(m.group(3)); sols += int(m.group(5))
        elif f: fin_seen = True; sols += int(f.group(4))
        else: other += 1
        if 'SOLUTION' in line: problems.append(f'hostB res{s}: SOLUTION')
    ids = np.arange(s, last + 1, 300)
    if len(ids) != done: problems.append(f'hostB res{s}: done {done} != ids up to last {len(ids)}')
    raw[ids] += 1
    sel = ids[ids < M]
    if len(sel) != len(np.arange(s, M, 300)): problems.append(f'hostB res{s}: does not reach 3.6M (last {last})')
    assigned[sel] += 1
for s in range(740):
    fdone = None
    for line in open(os.path.join(xd, f'res{s}.txt')):
        line = line.rstrip('\n'); m = prog.match(line); f = fin.match(line)
        if m:
            if int(m.group(1)) != s: problems.append(f'x res{s}: slice id {m.group(1)}')
            sols += int(m.group(5))
        elif f:
            if int(f.group(1)) != s: problems.append(f'x res{s}: slice id {f.group(1)}')
            fdone = int(f.group(2)); sols += int(f.group(4))
        else: other += 1
        if 'SOLUTION' in line: problems.append(f'x res{s}: SOLUTION')
    first = M + ((s - M) % 740)
    ids = np.arange(first, N, 740)
    if fdone is None: problems.append(f'x res{s}: no FINISHED')
    elif fdone != len(ids): problems.append(f'x res{s}: done {fdone} != {len(ids)}')
    else:
        raw[ids] += 1; assigned[ids] += 1
once = int(np.count_nonzero(assigned == 1)); zero = int(np.count_nonzero(assigned == 0)); multi = int(np.count_nonzero(assigned > 1))
print(f"ids 0..{N-1}: decided exactly once under the rule: {once}; never: {zero}; more than once: {multi}")
print(f"raw coverage (any slice, incl. hostB overlap past 3.6M): min {int(raw.min())}, ids decided twice: {int(np.count_nonzero(raw == 2))}")
print(f"solutions reported: {sols}; non-progress/FINISHED lines: {other}; problems: {len(problems)}")
for p in problems[:10]: print("PROBLEM", p)
print("EXACT COVERAGE PROVEN" if (once == N and zero == 0 and multi == 0 and sols == 0 and other == 0 and not problems and raw.min() >= 1) else "COVERAGE FAILED")
