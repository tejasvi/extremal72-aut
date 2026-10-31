"""Summarise sample-part logs: per part, nodes at levels > SPL (the part's own subtree) and user CPU; estimate of
the total tree = NPART * mean + nodes at levels <= SPL (prefix, counted once).  Usage: partsum.py SPL NPART LOGS..."""
import sys, re, statistics as st
spl = int(sys.argv[1]); npart = int(sys.argv[2])
rows = []; prefix = None
for fn in sys.argv[3:]:
    txt = open(fn).read()
    if 'DONE' not in txt: continue
    lv = {}
    for m in re.finditer(r'LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+) kids (\d+) .* lhprune (\d+)', txt):
        lv[int(m.group(1))] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
    sub = sum(v[0] for t, v in lv.items() if t > spl)
    pre = sum(v[0] for t, v in lv.items() if t <= spl)
    prefix = pre
    user = None
    tf = fn.replace('.log', '.time')
    try:
        mm = re.search(r'user ([\d.]+)', open(tf).read()); user = float(mm.group(1))
    except Exception: pass
    rows.append((fn.split('/')[-1], sub, user, [lv[t][0] for t in sorted(lv) if t > spl and lv[t][0] > 0]))
for r in rows: print(f"{r[0]:28s} nodes>{spl} {r[1]:.4e} user {r[2]} per-level {r[3]}")
subs = [r[1] for r in rows]; us = [r[2] for r in rows if r[2] is not None]
if subs:
    mu = st.mean(subs); sd = st.stdev(subs) if len(subs) > 1 else 0
    print(f"n={len(subs)} mean {mu:.4e} sd {sd:.3e} (se {sd/len(subs)**0.5:.3e}); total est {npart*mu + prefix:.4e} "
          f"(+-{npart*sd/len(subs)**0.5:.2e}); prefix {prefix:.3e}; mean user {st.mean(us) if us else 0:.1f} s; "
          f"est CPU core-h {npart*st.mean(us)/3600 if us else 0:.0f}")
