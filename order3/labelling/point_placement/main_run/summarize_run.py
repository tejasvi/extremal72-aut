"""Summarise a run_list.sh work directory: codes done, SAT ids (alert), ERROR ids, time statistics.
Usage: summarize_run.py WORKDIR"""
import sys, os, glob, re
W = sys.argv[1]
nchunks = len(glob.glob(os.path.join(W, 'chunks', 'c_*'))); ndone = len(glob.glob(os.path.join(W, 'done', 'c_*')))
n = sat = err = unsat = 0; wall = 0.0; nodes = 0; satlines = []; errlines = []
for f in glob.glob(os.path.join(W, 'out', 'c_*.out')):
    for l in open(f):
        m = re.search(r'res=(\S+)', l)
        if not m: continue
        n += 1; r = m.group(1)
        if r == 'UNSAT': unsat += 1
        elif r == 'SAT': sat += 1; satlines.append(l.strip())
        else: err += 1; errlines.append(l.strip())
        mw = re.search(r'wall=([0-9.]+)', l); mn = re.search(r'nodes=(\d+)', l)
        if mw: wall += float(mw.group(1))
        if mn: nodes += int(mn.group(1))
print("chunks %d, done %d; codes with results %d: UNSAT %d, SAT %d, ERROR %d; total wall %.0f s (%.2f s/code), nodes %.3e" % (nchunks, ndone, n, unsat, sat, err, wall, wall / max(n, 1), nodes))
for l in satlines[:50]: print("SAT!!", l[:400])
for l in errlines[:20]: print("ERROR", l[:300])
