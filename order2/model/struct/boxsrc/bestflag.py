"""(box) print the FLAGFILE of the scan with the lowest model estimate for code CI (all scans in <HOME>/struct/scan)"""
import sys, glob, re, os
ci = sys.argv[1]; best = None
for fn in glob.glob(os.path.expanduser(f'<HOME>/struct/scan/y{ci}_*_key.txt')):
    t = open(fn).read(); e = re.search(r'  est ([\d.e+]+)', t); f = re.search(r'FLAGFILE (\S+)', t)
    if e and f and os.path.exists(f.group(1)):
        v = float(e.group(1))
        if best is None or v < best[0]: best = (v, f.group(1))
print(best[1] if best else '')
