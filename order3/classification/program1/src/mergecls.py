"""merge ebclass slice outputs: dedupe by key (field 2). Usage: mergecls.py out in1 in2 ..."""
import sys
seen = {}
for fn in sys.argv[2:]:
    for line in open(fn):
        p = line.split()
        if len(p) < 4: continue
        if p[1] not in seen: seen[p[1]] = line
with open(sys.argv[1], 'w') as f:
    for k in sorted(seen): f.write(seen[k])
print(len(seen), "classes")
