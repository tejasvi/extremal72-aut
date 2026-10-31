"""Tabulate logs/scan2 + logs/scan: per code, flags ranked by the checkability-key model estimate."""
import glob, re, os, collections
rows = collections.defaultdict(list)
for fn in glob.glob('<HOME>/c72/c2opt/struct/logs/scan2/*_key.txt') + glob.glob('<HOME>/c72/c2opt/struct/logs/scan/*_key.txt'):
    txt = open(fn).read()
    m = re.search(r'Y(\d+) \|G\|=(\d+) orbits=\d+ raw total ([\d.e+]+) raw/\|G\| ([\d.e+]+)', txt)
    if not m: continue
    ci, G, raw, rg = int(m.group(1)), int(m.group(2)), float(m.group(3)), float(m.group(4))
    e = re.search(r'  est ([\d.e+]+) complete-at\s+(\d+) \|O\|=\s*(\d+) wt\s+(\d+)', txt)
    if not e: continue
    est = float(e.group(1)); comp = int(e.group(2)); osz = int(e.group(3)); w = int(e.group(4))
    pk = re.search(r'peak L(\d+)', txt); pk = int(pk.group(1)) if pk else -1
    ls = re.search(r'L\* = (\d+)', txt); ls = int(ls.group(1)) if ls else -1
    tag = os.path.basename(fn).replace('_key.txt', '')
    rows[ci].append((est, raw, rg, comp, osz, w, pk, ls, tag, G))
for ci in sorted(rows):
    r = sorted(rows[ci])
    best = r[0]
    print(f"Y{ci:2d} |G|={best[9]:5d} nflags {len(r):3d} | best est {best[0]:.2e} raw {best[1]:.2e} raw/G {best[2]:.2e} peak L{best[6]} orbit|O|={best[4]} wt{best[5]} complete@{best[3]} L*={best[7]} [{best[8]}]"
          + (f" | 2nd {r[1][0]:.2e} [{r[1][8]}]" if len(r) > 1 else ''))
