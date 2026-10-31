"""Compile per-instance results into results/final_table.json and a text table."""
import sys, json, glob, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from summarize import parse
D = HERE
fpf = json.load(open(D + '/data/fpf41.json'))
struct = {(s['code'], s['cls']): s for s in json.load(open(D + '/data/structure.json'))}
p1 = json.load(open(D + '/results/p1_summary.json'))
wd = {}
for f in glob.glob(D + '/logs/wd_*.log'):
    for line in open(f):
        parts = line.split(' ', 2)
        if len(parts) == 3 and parts[2].startswith('{'):
            wd[parts[0]] = json.loads(parts[2])['kills_verified']
        elif len(parts) >= 3 and 'FAIL' in line:
            wd[parts[0]] = 'FAIL'
cert = {}
for f in glob.glob(D + '/logs/cert_*.log'):
    for line in open(f):
        if line.startswith('{'):
            r = json.loads(line)
            cert[r['name']] = r['complete_certificate']
rows = []
for f in fpf:
    for j, cl in enumerate(f['classes']):
        name = 'i72_c%02d_b%d' % (f['idx'], j)
        m = json.load(open(D + '/inst2/%s.json' % name))
        s = struct[(f['idx'], j)]
        r = p1.get('p1_%s.out' % name)
        src = 'single'
        if r is None:
            # aggregate split jobs
            outs = sorted(glob.glob(D + '/results/out2/p2_%s_j*.out' % name))
            ps = [parse(open(o).read()) for o in outs]
            if len(outs) == 64 and all(ps):
                nodes = [ps[0]['nodes_per_level'][t] if t < 9 else sum(p['nodes_per_level'][t] for p in ps) for t in range(18)]
                kids = [ps[0]['kids_per_level'][t] if t < 9 else sum(p['kids_per_level'][t] for p in ps) for t in range(18)]
                kt = m['k_t']
                r = dict(nsol=sum(p['nsol'] for p in ps), cpu=sum(p['cpu'] for p in ps), nodes=sum(nodes),
                         kills=sum(nodes[t] * (1 << kt[t]) - kids[t] for t in range(18)),
                         deepest=max(t for t in range(18) if nodes[t] > 0), nodes_per_level=nodes)
                src = 'split64@9'
        old = None
        po = D + '/logs/run_%s.out' % name
        if os.path.exists(po):
            q = parse(open(po).read())
            if q:
                old = dict(nsol=q['nsol'], cpu=q['cpu'])
        rows.append(dict(name=name, code=f['idx'], cls=j, aut=f['order'], class_size=cl['size'], centralizer=cl['centralizer'],
                         rank1b=s['rank1beta'], dimfix=s['dimfix'], nparam=s['nparam'], gauge=s['gauge'], N=m['N'],
                         ncons=m['ncons'], k_t=m['k_t'], sched=m['sched'], result=r, run=src, old_order=old,
                         witness_verified=wd.get(name), complete_cert=cert.get(name, False)))
json.dump(rows, open(D + '/results/final_table.json', 'w'), indent=1)
done = [r for r in rows if r['result']]
print('instances', len(rows), 'completed', len(done), 'solutions', sum(r['result']['nsol'] for r in done))
print('total cpu (new orders) %.1f s' % sum(r['result']['cpu'] for r in done))
print('old-order completed', sum(1 for r in rows if r['old_order']), 'old-order sols', sum(r['old_order']['nsol'] for r in rows if r['old_order']),
      'old cpu %.1f' % sum(r['old_order']['cpu'] for r in rows if r['old_order']))
print('witness-verified kills', sum(r['witness_verified'] for r in rows if isinstance(r['witness_verified'], int)),
      'instances', sum(1 for r in rows if isinstance(r['witness_verified'], int)),
      'FAIL', sum(1 for r in rows if r['witness_verified'] == 'FAIL'))
print('complete certificates', sum(1 for r in rows if r['complete_cert']))
print()
print('%-11s %6s %5s %4s %3s %3s %6s %10s %12s %3s %9s %9s %6s %6s' % ('instance', '|Aut|', 'class', 'cent', 'rk', 'N', 'ncons', 'nodes', 'kills', 'dl', 'cpu_s', 'old_cpu', 'wit', 'cert'))
for r in rows:
    res = r['result']
    print('%-11s %6d %5d %4d %3d %3d %6d %10s %12s %3s %9s %9s %6s %6s' % (r['name'][4:], r['aut'], r['class_size'], r['centralizer'], r['rank1b'], r['N'], r['ncons'],
          res['nodes'] if res else '-', res['kills'] if res else '-', res['deepest'] if res else '-',
          '%.2f' % res['cpu'] if res else '-', '%.2f' % r['old_order']['cpu'] if r['old_order'] else '-',
          r['witness_verified'], 'yes' if r['complete_cert'] else ''))
