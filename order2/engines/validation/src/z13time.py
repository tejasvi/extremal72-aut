"""z13time.py DIR : paired timing verdict (rc11 vs rc13) from z13_time.sh logs: per part the mean user time of the two
copies of each binary, the gain, the gain on the tail (prefix-only runs subtracted) and the output identity."""
import glob, os, re, sys, hashlib, collections
D = sys.argv[1]
T = collections.defaultdict(lambda: collections.defaultdict(list)); H = collections.defaultdict(set)
for f in glob.glob(f'{D}/*.time'):
    b = os.path.basename(f)[:-5]; m = re.match(r'(y\w+?)_(p\d+|pfx\d)_(lwe11rc1[13])_c\d+', b)
    if not m: continue
    tag = m.group(1) + '_' + m.group(2); eng = m.group(3)
    txt = open(f).read().split()
    if not txt: print('incomplete', b); continue
    T[tag][eng].append(float(txt[0]))
    if not m.group(2).startswith('pfx'):
        H[tag].add(hashlib.sha256(''.join(re.sub(r'time [0-9]*s', '', l) for l in open(f[:-5] + '.log') if l.startswith(('LEVEL', 'DONE', 'SOL', 'LBPRUNE'))).encode()).hexdigest()[:12])
mean = lambda v: sum(v) / len(v)
pfx = collections.defaultdict(list)
for tag, d in T.items():
    if '_pfx' in tag: pfx[tag.split('_')[0]].append((mean(d['lwe11rc11']), mean(d['lwe11rc13'])))
tot = collections.defaultdict(lambda: [0.0, 0.0])
for tag in sorted(T):
    if '_pfx' in tag: continue
    d = T[tag]; a = mean(d['lwe11rc11']); b = mean(d['lwe11rc13']); pk = tag.split('_')[0]
    pa = mean([x[0] for x in pfx[pk]]); pb = mean([x[1] for x in pfx[pk]])
    tot[pk][0] += a; tot[pk][1] += b
    print(f"{tag:12s} rc11 {a:7.2f} rc13 {b:7.2f} gain {100*(a-b)/a:5.1f}%  tail {100*((a-pa)-(b-pb))/(a-pa):5.1f}%  "
          f"{'identical' if len(H[tag]) == 1 else 'DIFFER'}  copies {d['lwe11rc11']} {d['lwe11rc13']}")
for pk, (a, b) in tot.items(): print(f"{pk}: rc11 {a:.1f} s, rc13 {b:.1f} s, gain {100*(a-b)/a:.1f}%  (prefix-only rc11 {mean([x[0] for x in pfx[pk]]):.1f} s)")
