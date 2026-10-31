"""Summarise <HOME>/struct/samples/<code>/sSnN_pP.log: per (code, S, N): parts done, mean/sd of nodes at levels > S,
estimate N*mean + prefix, mean user CPU, est core-h = N*mean_user/3600 (box CPU)."""
import os, re, glob, statistics as st, sys
base = os.path.expanduser('<HOME>/struct/samples')
groups = {}
for fn in glob.glob(base + '/*/*.log'):
    code = fn.split('/')[-2]; m = re.match(r's(\d+)n(\d+)_p(\d+)\.log', os.path.basename(fn))
    if not m: continue
    s, n, p = int(m.group(1)), int(m.group(2)), int(m.group(3))
    txt = open(fn).read()
    if 'DONE' not in txt or 'STOPPED' in txt: continue
    lv = {int(a): int(b) for a, b in re.findall(r'LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+)', txt)}
    sub = sum(v for t, v in lv.items() if t > s); pre = sum(v for t, v in lv.items() if t <= s)
    try: user = float(re.search(r'user ([\d.]+)', open(fn[:-4] + '.time').read()).group(1))
    except Exception: user = None
    groups.setdefault((code, s, n), []).append((sub, user, pre, p))
for (code, s, n), rows in sorted(groups.items()):
    subs = [r[0] for r in rows]; us = [r[1] for r in rows if r[1] is not None]
    mu = st.mean(subs); sd = st.stdev(subs) if len(subs) > 1 else 0; se = sd / len(subs) ** 0.5
    mx = max(subs)
    print(f"{code} s{s} n{n}: parts {len(rows)} mean {mu:.4e} sd {sd:.2e} max/mean {mx/mu if mu else 0:.2f} "
          f"total {n*mu + rows[0][2]:.4e} (+-{100*se/mu if mu else 0:.1f}%) user {st.mean(us):.1f}s "
          f"(max {max(us):.0f}s) core-h {n*st.mean(us)/3600:.0f} prefix {rows[0][2]:.3e}")
