"""Independent re-derivation (reviewer code, not csp5p's) of: octdod.txt Golay check; per-code F8/F12 from E;
optional planted F-mode instance writer.
usage: indep.py golay OCTDOD
       indep.py fam OCTDOD CODELINES_FILE [maxlines]          -> per line: pw8 pw10 pw12 f8 f12 (csp5p conventions)
       indep.py plant OCTDOD CODELINES_FILE LINEIDX SEED OUTPREFIX [nplant]
"""
import sys, random
import numpy as np

def read_blocks(path):
    v = [int(x) for x in open(path).read().split()]
    return v

def rank_f2(vecs):
    basis = {}
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                break
    return basis

def span_words(basis_vecs):
    words = [0]
    for b in basis_vecs:
        words += [w ^ b for w in words]
    return words

def golay_check(path):
    blk = read_blocks(path)
    print("nvalues", len(blk))
    octs, dods = blk[:759], blk[759:759 + 2576]
    assert len(blk) == 759 + 2576, len(blk)
    assert all(bin(o).count('1') == 8 and o < (1 << 24) for o in octs)
    assert all(bin(d).count('1') == 12 and d < (1 << 24) for d in dods)
    assert len(set(octs)) == 759 and len(set(dods)) == 2576
    B = rank_f2(octs)
    print("dim span(octads)", len(B))
    W = span_words(list(B.values()))
    wt = {}
    for w in W:
        c = bin(w).count('1'); wt[c] = wt.get(c, 0) + 1
    print("weight distribution of span", sorted(wt.items()))
    s8 = set(w for w in W if bin(w).count('1') == 8); s12 = set(w for w in W if bin(w).count('1') == 12)
    print("octads == weight-8 words:", s8 == set(octs), " dodecads == weight-12 words:", s12 == set(dods))
    o0 = octs[0]; print("O0 points", [i for i in range(24) if o0 >> i & 1])

def parse_line(line):
    t = line.split()[0]
    assert len(t) >= 192
    rows = []
    for r in range(12):
        a = int(t[16 * r:16 * r + 8], 16); b = int(t[16 * r + 8:16 * r + 16], 16)
        rows.append((a, b))
    idt = [f[3:] for f in line.split()[1:] if f.startswith('id=')]
    return rows, (idt[0] if idt else None)

def mulw(a, b):  # (a + b w) * w = b + (a+b) w
    return b, a ^ b

def all_supports(rows):
    # all 4^12 codewords; returns numpy uint32 array of supports (nonzero words only)
    def half(rs):
        lo = np.zeros(1, dtype=np.uint32); hi = np.zeros(1, dtype=np.uint32)
        for (a, b) in rs:
            a2, b2 = mulw(a, b); a3, b3 = mulw(a2, b2)
            lo = np.concatenate([lo, lo ^ np.uint32(a), lo ^ np.uint32(a2), lo ^ np.uint32(a3)])
            hi = np.concatenate([hi, hi ^ np.uint32(b), hi ^ np.uint32(b2), hi ^ np.uint32(b3)])
        return lo, hi
    lA, hA = half(rows[:6]); lB, hB = half(rows[6:])
    sup = (lA[:, None] ^ lB[None, :]) | (hA[:, None] ^ hB[None, :])
    sup = sup.ravel()[1:]  # drop the zero word (i=0,j=0)
    return sup

def families(rows):
    sup = all_supports(rows)
    wt = np.bitwise_count(sup)
    dmin = int(wt.min())
    s8 = sup[wt == 8]; s10 = sup[wt == 10]; s12 = sup[wt == 12]
    F8 = set()
    for S in set(int(x) for x in s8):
        F8.add(S)
        ins = [i for i in range(24) if S >> i & 1]; outs = [i for i in range(24) if not S >> i & 1]
        for y in ins:
            for b in outs:
                F8.add((S & ~(1 << y)) | (1 << b))
    for S in set(int(x) for x in s10):
        ins = [i for i in range(24) if S >> i & 1]
        for i in range(10):
            for j in range(i + 1, 10):
                F8.add(S & ~(1 << ins[i]) & ~(1 << ins[j]))
    F12 = set(int(x) for x in s12)
    return dmin, len(s8), len(s10), len(s12), F8, F12

def herm_ok(rows):
    # Hermitian self-orthogonality via explicit F4 arithmetic (elements 0,1,w,w^2 as (a,b))
    def el(r, i):
        return ((r[0] >> i) & 1) | (((r[1] >> i) & 1) << 1)
    mul = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
    conj = [0, 1, 3, 2]
    for u in rows:
        for v in rows:
            s = 0
            for i in range(24):
                s ^= mul[el(u, i)][conj[el(v, i)]]
            if s:
                return False
    return True

def main():
    cmd = sys.argv[1]
    if cmd == 'golay':
        golay_check(sys.argv[2]); return
    lines = [l for l in open(sys.argv[3]) if l.strip()]
    if cmd == 'fam':
        mx = int(sys.argv[4]) if len(sys.argv) > 4 else len(lines)
        for li, l in enumerate(lines[:mx]):
            rows, idt = parse_line(l)
            hb = any((a | b) >> 24 for a, b in rows)
            dmin, n8, n10, n12, F8, F12 = families(rows)
            print("id=%s herm=%d highbits=%d dmin=%d pw8=%d pw10=%d pw12=%d f8=%d f12=%d dist8sup=%d dist12sup=%d" % (
                idt, herm_ok(rows), hb, dmin, n8 // 3, n10 // 3, n12 // 3, len(F8), len(F12), n8 // 3, len(F12)))
            sys.stdout.flush()
        return
    if cmd == 'plant':
        li = int(sys.argv[4]); seed = int(sys.argv[5]); pref = sys.argv[6]; npl = int(sys.argv[7]) if len(sys.argv) > 7 else 1
        rows, idt = parse_line(lines[li])
        dmin, n8, n10, n12, F8, F12 = families(rows)
        blk = read_blocks(sys.argv[2])
        rng = random.Random(seed)
        planted = []
        for t in range(npl):
            sig = list(range(24)); rng.shuffle(sig)
            img = lambda m: sum(1 << sig[i] for i in range(24) if m >> i & 1)
            o = [img(m) for m in blk[:759]]; d = [img(m) for m in blk[759:]]
            c8 = sum(1 for x in o if x in F8); c12 = sum(1 for x in d if x in F12)
            F8.difference_update(o); F12.difference_update(d)
            B = rank_f2(o)
            # reduced row echelon, pivots from bit 23 down
            R = sorted(B.values(), reverse=True)
            for i in range(len(R)):
                h = R[i].bit_length() - 1
                for j in range(len(R)):
                    if j != i and (R[j] >> h) & 1:
                        R[j] ^= R[i]
            R = sorted(R, reverse=True)
            planted.append((sig, c8, c12, ",".join("%06x" % x for x in R)))
        for t, (sig, c8, c12, g) in enumerate(planted):
            print("planted %d cleared8=%d cleared12=%d golay=%s sigma=%s" % (t, c8, c12, g, ",".join(map(str, sig))))
        for name, F in (("f8", F8), ("f12", F12)):
            bm = np.zeros(1 << 21, dtype=np.uint8)
            for m in F:
                bm[m >> 3] |= np.uint8(1 << (m & 7))
            bm.tofile(pref + "." + name + ".raw")
        print("wrote", pref, "f8", len(F8), "f12", len(F12))
        return

main()
