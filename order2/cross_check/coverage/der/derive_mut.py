"""Projected ("coset-death") constraints for an lwe instance (sat).  Precise rule, for independent audit.

Instance (mkinst.py format).  Variables x in F2^N; variable v has level lev(v) (vstart).  Constraint c has m forms
f_1..f_m (masks over the N variables), constants a_1..a_m and a set Bad_c of m-bit values; a solution satisfies
    s_c(x) = (<f_j, x> + a_j)_{j=1..m}  not in Bad_c.                                             (C)
lv(c) = max level of a variable in some f_j.

Derivation, for each constraint c and each level t = 0 .. lv(c)-1:
  1. Restrict the forms to the variables of level > t: f_j^> = f_j AND mask(level > t).
  2. K_t = left kernel {phi in F2^m : XOR_{j: phi_j=1} f_j^> = 0}; basis phi_1..phi_q from Gaussian elimination over
     the rows in index order (left_kernel below).  If q = 0, or q equals the q of the previous t, go to the next t.
  3. Derived forms and constants: g_k = XOR_{j: phi_kj=1} f_j, b_k = XOR_{j: phi_kj=1} a_j (k = 1..q).  By step 2,
     every g_k uses only variables of level <= t.  Zero masks g_k = 0 are kept (constant syndrome bits).
  4. Phi(s)_k = <phi_k, s>.  For every x: Phi(s_c(x)) = (<g_k, x> + b_k)_k =: w(x).
  5. BadW = {w in F2^q : every s in F2^m with Phi(s) = w lies in Bad_c}  (computed as the complement of
     {Phi(s) : s not in Bad_c}).
  Derived constraint (D):  w(x) not in BadW.
Implication (soundness): if x satisfies (C), then s_c(x) is an element of Phi^-1(w(x)) that is not in Bad_c, so
Phi^-1(w(x)) is not contained in Bad_c, i.e. w(x) is not in BadW: x satisfies (D).  The argument is pointwise, so
adding (D) never removes a solution, and any symmetry-breaking argument that holds for the solution set (LTS) is
unaffected.  (Strength, not needed for soundness: once all variables of level <= t are fixed, the values of s_c over
all completions form the coset s0 + Im(F^>), which equals Phi^-1(w) because q = m - rank(F^>); so (D) is then the
exact test "the whole remaining coset of c is bad".)
Selection (affects only speed): (D) is kept iff BadW contains a reachable value (a w consistent with the linear
dependencies among the g_k and the constants b_k).  dl = max level of a variable in the g_k (0 if none); (D) is
dropped if dl >= lv(c); among the t giving the same dl, the largest t wins (its kernel contains the smaller ones).
Options --minlev/--maxlev keep only dl in [minlev, maxlev].

Output OUT (same format as the input; readable by lwe8 .. rc9): header "N NLEV NC", vstart line, then per constraint
"lv wt m nbad", m lines "hexmask const", one line of bad values.  Originals are unchanged; a derived constraint has
lv = dl, wt = wt(c) - 1 (wt only orders constraints within a level), m = q, forms g_k/b_k, bad = sorted BadW over all
of F2^q.  All constraints are sorted by (lv, derived after original, original index / derived serial).
Side files: OUT.map (one line: new index of each original constraint, in original order), OUT.derived (one line per
derived constraint k: source index, t, dl, q, #reachable bad w, #reachable w), and with --meta OUT.meta (the
original .meta lines in the new order; derived constraint k gets the line "-1-k", so symprep3 never maps a key or
orbit word to it).  An LTSH file must be regenerated for OUT (src/mkltsh.py), since constraint indices move.

Usage: derive.py INST OUT [--meta | --synthmeta] [--minlev L] [--maxlev L]"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, '<HOME>/c72/c2opt/sat/src')
import enc

def left_kernel(rows):
    """rows: list of ints (vectors).  Returns basis of {phi : XOR_{i in phi} rows[i] = 0} as int masks over indices."""
    ech = []                     # (pivot bit, vec, combo)
    ker = []
    for i, v in enumerate(rows):
        cmb = 1 << i
        for p, e, ce in ech:
            if v & p: v ^= e; cmb ^= ce
        if v: ech.append((v & -v, v, cmb))
        else: ker.append(cmb)
    return ker

def apply_combo(phi, fm, fc):
    f = 0; c = 0; k = 0
    while phi:
        if phi & 1: f ^= fm[k]; c ^= fc[k]
        phi >>= 1; k += 1
    return f, c

def derive_con(lv, m, fm, fc, bad, vstart, levof):
    good = np.array([s for s in range(1 << m) if s not in bad], dtype=np.int64)
    out = {}
    prevq = -1
    for t in range(lv):
        hi = ~((1 << vstart[t + 1]) - 1)
        ker = left_kernel([f & hi for f in fm])
        q = len(ker)
        if q == prevq or q == 0: prevq = q; continue
        prevq = q
        # derived forms; split constant (zero-form) combinations
        df = [apply_combo(phi, fm, fc) for phi in ker]
        # reduce to independent nonzero forms: combos of derived forms that vanish are constants
        # w-values: compute goodW over all q bits, then restrict to reachable w
        W = np.zeros(len(good), dtype=np.int64)
        for k, phi in enumerate(ker):
            W |= (np.bitwise_count(good & phi) & 1).astype(np.int64) << k
        goodW = set(W.tolist())
        # reachable w: w = (forms . x) ^ consts; dependencies among derived forms fix parities
        deps = left_kernel([f for f, _ in df])
        cvec = sum(c << k for k, (_, c) in enumerate(df))
        dcon = [(d, (d & cvec).bit_count() & 1) for d in deps]
        reach = [w for w in range(1 << q) if all(((w & d).bit_count() & 1) == v for d, v in dcon)]
        badr = [w for w in reach if w not in goodW]
        if not badr: continue
        dl = max((levof[v] for f, _ in df for v in range(f.bit_length()) if (f >> v) & 1), default=0)
        if dl >= lv: continue
        # MUTANT (audit control): w is called bad if SOME element of its coset is bad (unsound)
        badarr = np.array(sorted(bad), dtype=np.int64); WB = np.zeros(len(badarr), dtype=np.int64)
        for k, phi in enumerate(ker):
            WB |= (np.bitwise_count(badarr & phi) & 1).astype(np.int64) << k
        out[dl] = (t, q, df, sorted(set(WB.tolist())), len(badr), len(reach))   # larger t overwrites
    return out

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('inst'); ap.add_argument('out'); ap.add_argument('--maxlev', type=int, default=99); ap.add_argument('--minlev', type=int, default=0)
    ap.add_argument('--meta', action='store_true', help='also write OUT.meta (original meta lines; derived: -1-k)')
    ap.add_argument('--synthmeta', action='store_true', help='write OUT.meta with the original index as the token of '
                    'original rows (for instances without .meta; not usable by symprep3)')
    a = ap.parse_args()
    meta = open(a.inst + '.meta').read().rstrip('\n').split('\n') if a.meta else None
    N, NLEV, vstart, cons = enc.parse(a.inst)
    levof = [0] * N
    for t in range(NLEV):
        for v in range(vstart[t], vstart[t + 1]): levof[v] = t
    allc = []          # (lv, wt, forms[(mask, c)], bad list)
    info = []
    for idx, (lv, wt, m, fm, fc, bad) in enumerate(cons):
        allc.append((lv, wt, list(zip(fm, fc)), sorted(bad), 0, idx))
        if lv == 0: continue
        for dl, (t, q, df, badall, nbr, nr) in derive_con(lv, m, fm, fc, bad, vstart, levof).items():
            if dl > a.maxlev or dl < a.minlev: continue
            allc.append((dl, wt - 1, df, badall, 1, len(info)))
            info.append(f"{idx} {t} {dl} {q} {nbr} {nr}")
    allc.sort(key=lambda c: (c[0], c[4], c[5]))
    if a.synthmeta and meta is None: meta = [str(i) for i in range(len(cons))]
    if meta is not None:
        mo = [meta[c[5]] if c[4] == 0 else str(-1 - c[5]) for c in allc]
        open(a.out + '.meta', 'w').write('\n'.join(mo) + '\n')
    if True:
        omap = [None] * len(cons)
        for k, c in enumerate(allc):
            if c[4] == 0: omap[c[5]] = k
        open(a.out + '.map', 'w').write(' '.join(map(str, omap)) + '\n')
    lines = [f"{N} {NLEV} {len(allc)}", ' '.join(map(str, vstart))]
    for (lv, wt, forms, bad, _d, _i) in allc:
        lines.append(f"{lv} {wt} {len(forms)} {len(bad)}")
        for (f, c) in forms: lines.append(f"{f:x} {c}")
        lines.append(' '.join(map(str, bad)))
    open(a.out, 'w').write('\n'.join(lines) + '\n')
    open(a.out + '.derived', 'w').write('\n'.join(info) + '\n')
    from collections import Counter
    cnt = Counter(int(s.split()[2]) for s in info)
    print(f"derived {len(info)} constraints; by level {dict(sorted(cnt.items()))}; total {len(allc)}", flush=True)

if __name__ == '__main__':
    main()
