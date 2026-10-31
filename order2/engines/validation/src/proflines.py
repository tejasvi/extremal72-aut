"""proflines.py BIN TOP.txt [N] : line shares (first frame inside the engine source) of a PC profile."""
import subprocess, collections, sys
binp, topf = sys.argv[1], sys.argv[2]; N = int(sys.argv[3]) if len(sys.argv) > 3 else 40
top = [l.split() for l in open(topf)]
tot = sum(int(n) for n, _ in top)
lines = collections.Counter()
for n, a in top:
    out = subprocess.run(['addr2line', '-i', '-e', binp, a], capture_output=True, text=True).stdout.split('\n')
    loc = next((o for o in out if '.c:' in o and '/usr/' not in o), out[0])
    lines[loc.split('/')[-1].split(' ')[0]] += int(n)
src = None
for loc, n in lines.most_common(N):
    f, ln = loc.split(':') if ':' in loc else (loc, '0')
    txt = ''
    try:
        txt = open(f).read().split('\n')[int(ln) - 1].strip()[:110]
    except Exception: pass
    print(f'{100*n/tot:5.1f}% {loc:28s} {txt}')
