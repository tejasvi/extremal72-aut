"""Refined checkability analysis: for each level L, the G-orbits of low words that are COMPLETELY checkable at
level L (all words have constraint level < L) and their total syndrome bits (wt 8: 10, wt 10: 8, wt 12: 6 free
bits per word).  L* = first level at which complete orbits provide >= log2|G| + MARGIN bits (a key made of words
of these orbits makes every LTS comparison decidable at L*; extra bits make ties rare).
Estimates: est_ub = sum_{t<L*} raw_t + sum_{t>=L*} raw_t/|G|  (no pruning before L*: upper-bound style),
           est_lo = raw/|G|.  Usage: keycheck2.py CI INSTANCE RAWPROF [MARGIN]"""
import sys, os, pickle, math
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst
from keycheck import closure_size, orbits, read_raw
ci = int(sys.argv[1]); I = read_inst(sys.argv[2]); raw = read_raw(sys.argv[3]); MARGIN = float(sys.argv[4]) if len(sys.argv) > 4 else 8
perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
nG = closure_size(perms); obs = orbits(I['cons'], perms)
bits = {8: 10, 10: 8, 12: 6}
need = math.log2(nG) + MARGIN
Ls = None; rows = []
for L in range(I['NLEV'] + 1):
    comp = [o for o in obs if max(o['levels']) < L]
    b = sum(bits[o['wt']] * len(o['words']) for o in comp)
    rows.append((L, len(comp), sum(len(o['words']) for o in comp), b))
    if Ls is None and b >= need: Ls = L
peak = max(range(len(raw)), key=lambda t: raw[t])
rawtot = sum(raw)
ub = sum(raw[t] for t in range(min(Ls, len(raw)))) + sum(raw[t] / nG for t in range(Ls, len(raw))) if Ls is not None else rawtot
print(f"Y{ci} |G|={nG} raw {rawtot:.3e} peak L{peak} raw/|G| {rawtot/nG:.3e} need {need:.1f} bits -> L* = {Ls} est_ub {ub:.3e}")
print("  L: (#complete orbits, #words, bits) " + ' '.join(f"{L}:({a},{w},{b})" for L, a, w, b in rows[:12]))
