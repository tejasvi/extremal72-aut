"""Aggregate csp5p production results: completeness over ids 0..N-1, SAT/ERROR lists, totals.
Usage: aggregate.py N RESULT_TGZ_OR_DIR [...]   (tgz files from boxctl.sh pull, or directories of .out files)"""
import sys, os, re, tarfile, glob
N = int(sys.argv[1])
seen = bytearray(N); dup = 0; bad = 0; sat = []; err = []; unsat = 0; wall = 0.0; nodes = 0; maxwall = (0.0, None)
idre = re.compile(r'^id=(\d+) res=(\S+)'); wre = re.compile(r' wall=([0-9.]+)'); nre = re.compile(r' nodes=(\d+)')
def lines_of(src):
    if os.path.isdir(src):
        for f in glob.glob(os.path.join(src, '**', '*.out'), recursive=True):
            with open(f, errors='replace') as fh:
                for l in fh: yield l
    else:
        with tarfile.open(src) as t:
            for m in t:
                if m.isfile() and m.name.endswith('.out'):
                    for l in t.extractfile(m).read().decode(errors='replace').splitlines(): yield l
for src in sys.argv[2:]:
    for l in lines_of(src):
        m = idre.match(l)
        if not m: continue
        i = int(m.group(1)); r = m.group(2)
        if i < 0 or i >= N: bad += 1; continue
        if seen[i]: dup += 1
        seen[i] = 1
        if r == 'UNSAT': unsat += 1
        elif r == 'SAT': sat.append(l.strip())
        else: err.append(l.strip())
        mw = wre.search(l); mn = nre.search(l)
        if mw:
            w = float(mw.group(1)); wall += w
            if w > maxwall[0]: maxwall = (w, i)
        if mn: nodes += int(mn.group(1))
missing = N - sum(seen)
print("N=%d covered=%d missing=%d duplicate_lines=%d out_of_range=%d" % (N, N - missing, missing, dup, bad))
print("UNSAT=%d SAT=%d ERROR=%d total_wall=%.0f s (%.2f s/code) nodes=%.4e slowest=%.1f s (id %s)" % (unsat, len(sat), len(err), wall, wall / max(1, N - missing), nodes, maxwall[0], maxwall[1]))
if missing and missing < 50: print("missing ids:", [i for i in range(N) if not seen[i]])
for l in sat[:20]: print("SAT!!", l[:500])
for l in err[:20]: print("ERROR", l[:300])
