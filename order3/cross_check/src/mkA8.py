# build A8 array (uint16) indexed by cls24 line from the gz list (streamed)
import sys, gzip, numpy as np
a = np.zeros(13485816, dtype=np.uint16); n = 0
with gzip.open(sys.argv[1], 'rt') as f:
    for line in f:
        a[n] = int(line.split()[2]); n += 1
assert n == 13485816, n
a.tofile(sys.argv[2]); print('lines', n)
