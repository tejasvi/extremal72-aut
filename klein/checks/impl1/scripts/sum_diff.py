"""Summarise the differential-test logs (SUMMARY lines) copied from the box into diff_box/."""
import glob, ast, collections, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
tot = collections.Counter(); rows = []
for f in sorted(glob.glob(HERE + '/../diff_box/*.log')):
    s = [l for l in open(f) if l.startswith('SUMMARY')]
    bad = [l.strip() for l in open(f) if l.startswith(('MISMATCH', 'PLANT NOT', 'SPLIT MISMATCH'))]
    if not s: rows.append((f.split('/')[-1], 'NO SUMMARY')); continue
    m = re.match(r'SUMMARY (\S+) (\S+) L (\d+) prefixes (\d+) (\{.*\})', s[0])
    d = ast.literal_eval(m.group(5)); tot.update(d); tot['prefixes'] += int(m.group(4)); tot['configs'] += 1
    rows.append((m.group(1), f"L{m.group(3)} prefixes {m.group(4)} tests {d['tests']} mism {d['mismatches']} sols {d['sols']} nodes {d['nodes']} planted {d['planted_found']}/{d['planted']} split {d['split_ok']}/{d['split_ok'] + d['split_bad']} timeouts {d.get('timeouts', 0)}" + (f' BAD {bad[:2]}' if bad else '')))
for r in rows: print(*r)
print('TOTAL', dict(tot))
