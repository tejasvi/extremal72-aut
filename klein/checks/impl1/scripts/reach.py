"""Reachable bad syndromes per constraint: bad cap (c + column span of the linear part).  Aggregated by weight."""
import sys, collections
def main():
    fn = sys.argv[1]
    lines = open(fn).read().split('\n')
    N, NL, NC = map(int, lines[0].split())
    pos = 2; agg = collections.defaultdict(lambda: [0, 0, 0, 0])
    for c in range(NC):
        lv, wt, m, nb = map(int, lines[pos].split()); pos += 1
        forms = []
        for s in range(m): hx, cc = lines[pos].split(); pos += 1; forms.append((int(hx, 16), int(cc)))
        bad = list(map(int, lines[pos].split())); pos += 1
        c0 = sum(cc << s for s, (vm, cc) in enumerate(forms))
        piv = {}
        for v in range(N):
            col = sum(((vm >> v) & 1) << s for s, (vm, cc) in enumerate(forms))
            for b, r in piv.items():
                if (col >> b) & 1: col ^= r
            if col:
                hb = col.bit_length() - 1
                for b2 in list(piv):
                    if (piv[b2] >> hb) & 1: piv[b2] ^= col
                piv[hb] = col
        def inspan(x):
            for b, r in piv.items():
                if (x >> b) & 1: x ^= r
            return x == 0
        nreach = sum(1 for b in bad if inspan(b ^ c0))
        a = agg[wt]; a[0] += 1; a[1] += (nreach > 0); a[2] = max(a[2], nreach); a[3] += nreach
    print(fn.split('/')[-1], ' '.join(f'w{w}: cons {a[0]} with_reachable_bad {a[1]} max_reach {a[2]} sum_reach {a[3]};' for w, a in sorted(agg.items())))
main()
