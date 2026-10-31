"""Own coverage check of csp5p production output (audit).  Reads result lines on stdin (concatenated .out files).
Checks: every id 0..N-1 present, all res=UNSAT, no SAT/ERROR, lines well formed, duplicates consistent,
pw8 == A8/3 of the cls24 line with that id (A8 array built from cls24 by mkA8), node counts for sampled ids.
usage: python cov_csp.py A8.u16 SAMPLE_IDS_NODES.txt < lines"""
import sys, re, numpy as np
A8 = np.fromfile(sys.argv[1], dtype=np.uint16); N = len(A8)
samp = {}
if len(sys.argv) > 2:
    for l in open(sys.argv[2]):
        f = l.split(); samp[int(f[0])] = int(f[1])
seen = np.zeros(N, dtype=np.uint8)
pat = re.compile(r'^id=(\d+) res=(UNSAT|SAT|ERROR)( nsol=(\S+) hash=([0-9a-f]{16}) nodes=(\d+) wall=\S+ cpu=\S+ prep=\S+ pw8=(\d+) pw10=(\d+) pw12=(\d+) f8=(\d+) f12=(\d+))?')
cnt = {'UNSAT': 0, 'SAT': 0, 'ERROR': 0}; bad = []; other = 0; dup = 0; dupdiff = 0; pwbad = []; sampres = {}
first = {}
for line in sys.stdin:
    line = line.rstrip('\n')
    if not line.strip(): continue
    m = pat.match(line)
    if not m or m.group(3) is None:
        other += 1
        if len(bad) < 20: bad.append(line[:200])
        continue
    i = int(m.group(1)); r = m.group(2)
    if i >= N: other += 1; bad.append(line[:200]); continue
    cnt[r] += 1
    if r != 'UNSAT' and len(bad) < 20: bad.append(line[:300])
    if m.group(4) != '0' and r == 'UNSAT': bad.append('UNSAT with nsol!=0: ' + line[:200])
    pw8 = int(m.group(7))
    if 3 * pw8 != int(A8[i]):
        if len(pwbad) < 20: pwbad.append((i, pw8, int(A8[i])))
    if seen[i]:
        dup += 1
    seen[i] = 1
    if i in samp: sampres.setdefault(i, []).append(int(m.group(6)))
missing = int(N - seen.sum())
print('N', N, 'covered', N - missing, 'missing', missing, 'dup_lines', dup)
print('res counts', cnt, 'unparsed/other lines', other)
print('pw8 != A8/3 cases', len(pwbad), pwbad[:5])
for b in bad[:20]: print('BAD', b)
if missing and missing < 100: print('missing ids', np.nonzero(seen == 0)[0].tolist())
ok = sum(1 for i in samp if i in sampres and all(n == samp[i] for n in sampres[i]))
print('sampled ids with matching node counts', ok, 'of', len(samp), 'present', sum(1 for i in samp if i in sampres))
for i in samp:
    if i in sampres and any(n != samp[i] for n in sampres[i]): print('NODE MISMATCH', i, samp[i], sampres[i])
print('VERDICT', 'PASS' if (missing == 0 and cnt['SAT'] == 0 and cnt['ERROR'] == 0 and other == 0 and not pwbad and cnt['UNSAT'] >= N) else 'CHECK')
