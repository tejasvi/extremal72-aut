"""Convert c3explore code lines (layout A: 24 hex tokens lo hi ..., optional '| ...') to layout B (gtest4:
12 x (8 hex a + 8 hex b) concatenated), keeping line order; appends ' id=<tag>'.  Usage: toB.py IN OUT TAG [first [count]]"""
import sys
src, dst, tag = sys.argv[1], sys.argv[2], sys.argv[3]
first = int(sys.argv[4]) if len(sys.argv) > 4 else 0
count = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 9
out = open(dst, 'w'); n = 0
for i, line in enumerate(open(src)):
    if i < first: continue
    if n >= count: break
    toks = line.split('|')[0].split()
    if len(toks) < 24: continue
    vals = [int(t, 16) for t in toks[:24]]
    out.write(''.join('%08x%08x' % (vals[2 * r], vals[2 * r + 1]) for r in range(12)) + ' id=%s:%d\n' % (tag, i))
    n += 1
print(dst, n, "codes")
