"""Parse engine outputs: per-instance nsol, cpu, nodes, kills, deepest level."""
import glob, os, json, sys, collections

def parse(txt):
    if 'END' not in txt:
        return None
    st = [l for l in txt.splitlines() if l.startswith('STATS')][0].split()
    nsol = int(st[2]); cpu = float(st[4])
    levels = [l.split() for l in txt.splitlines() if l.startswith('LEVEL')]
    per = [(int(l[1]), int(l[3]), int(l[5]), int(l[7]), int(l[9]), int(l[11])) for l in levels]
    nodes = sum(p[3] for p in per)
    kills = sum(p[3] * (1 << p[1]) - p[4] for p in per)
    deepest = max([p[0] for p in per if p[3] > 0], default=-1)
    return dict(nsol=nsol, cpu=cpu, nodes=nodes, kills=kills, deepest=deepest,
                nodes_per_level=[p[3] for p in per], kids_per_level=[p[4] for p in per],
                coneval=sum(p[5] for p in per))

if __name__ == '__main__':
    pat = sys.argv[1]
    rows = {}
    for f in sorted(glob.glob(pat)):
        rows[os.path.basename(f)] = parse(open(f).read())
    done = {k: v for k, v in rows.items() if v}
    print('files', len(rows), 'completed', len(done), 'total cpu %.1f' % sum(v['cpu'] for v in done.values()),
          'sols', sum(v['nsol'] for v in done.values()))
    print('deepest level distribution', sorted(collections.Counter(v['deepest'] for v in done.values()).items()))
    if done:
        print('max cpu', max((v['cpu'], k) for k, v in done.items()))
        print('max nodes', max((v['nodes'], k) for k, v in done.items()))
        print('total nodes', sum(v['nodes'] for v in done.values()), 'total kills', sum(v['kills'] for v in done.values()))
    if len(sys.argv) > 2:
        json.dump(rows, open(sys.argv[2], 'w'), indent=0)
