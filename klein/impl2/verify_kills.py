"""Independent verification of engine kills: for each reported killed child, exhibit an explicit codeword
of weight < d that lies in the code for every completion (checked for the zero completion and two random ones).
Usage: verify_kills.py <instance json (with order)> <instance txt> <engine output with KILL lines> [d]"""
import sys, json, random, hashlib, os
HERE = os.path.dirname(os.path.abspath(__file__))
from itertools import combinations
sys.path.insert(0, HERE)
from gf2 import *
from instance import Instance
from export import export, export_cons, gram_from_x, build_code
from structure import solve_affine

def main(meta_path, txt_path, out_path, d=16):
    meta = json.load(open(meta_path))
    codes = json.load(open(HERE + '/data/codes41.json'))
    Yb = codes[meta['code'] - 1]['basis']
    I = Instance(Yb, meta['beta'], d)
    I.set_order(meta['order'])
    # regenerate the engine file and compare
    tmp = '/tmp/v4i_verify_%d.txt' % random.randrange(1 << 30)
    export(I, tmp)
    same = open(tmp).read() == open(txt_path).read()
    assert same, "regenerated instance differs from engine input"
    cons = export_cons(I)
    vstart = [0]
    for t in range(I.k):
        vstart.append(vstart[-1] + I.k_t[t])
    n2 = I.n2
    one = (1 << n2) - 1
    rng = random.Random(7)
    kills = [l.split() for l in open(out_path) if l.startswith("KILL")]
    per_level = {}
    per_weight = {}
    per_ewt = {}
    for parts in kills:
        t, ci, v = int(parts[1]), int(parts[2]), int(parts[3])
        X = (int(parts[4], 16) << 64) | int(parts[5], 16)
        X |= v << vstart[t]
        assert X >> vstart[t + 1] == 0
        lev, _, w, cm, dvec, bad, y = cons[ci]
        assert lev == t and I.coords(y) == cm and popcount(y) == w
        xb = [(X >> s) & 1 for s in range(I.N)]
        G = gram_from_x(I, xb)
        k = I.k
        row = [0] * k
        for i in range(k):
            if (cm >> i) & 1:
                for l in range(k):
                    row[l] ^= G[i][l]
        z0 = solve_affine([(I.w[l], row[l]) for l in range(k)], n2)[0]
        S = y; Sc = one ^ S
        E = [j for j in range(d) if 2 * j < d - w and j % 2 == (w // 2) % 2]
        punct = Span([b & Sc for b in I.yb0])
        comp = [i for i in range(n2) if (Sc >> i) & 1]
        wit = None
        for j in E:
            for es in combinations(comp, j):
                e = 0
                for i in es:
                    e |= 1 << i
                if punct.contains((z0 ^ e) & Sc):
                    wit = e; break
            if wit is not None:
                break
        assert wit is not None, ("no witness for kill", parts)
        # find x in Y with (z0 ^ x) & Sc == wit
        eqs = []
        # unknown coefficients a over basis yb0: sum a_i (b_i & Sc) = (z0 ^ wit) & Sc
        target = (z0 ^ wit) & Sc
        for bit in comp:
            m = 0
            for i, b in enumerate(I.yb0):
                if (b >> bit) & 1:
                    m |= 1 << i
            eqs.append((m, (target >> bit) & 1))
        a = solve_affine(eqs, len(I.yb0))[0]
        x = 0
        for i, b in enumerate(I.yb0):
            if (a >> i) & 1:
                x ^= b
        z = z0 ^ x
        assert z & Sc == wit
        cw = z | ((z ^ y) << n2)
        wt = popcount(cw)
        assert wt < d and wt % 4 == 0 and wt == w + 2 * popcount(wit)
        # membership for zero completion and two random completions of later variables
        for trial in range(3):
            xb2 = list(xb)
            if trial > 0:
                for s in range(vstart[t + 1], I.N):
                    xb2[s] = rng.randrange(2)
            rows = build_code(I, gram_from_x(I, xb2))
            assert Span(rows).contains(cw), "witness not in code"
        per_level[t] = per_level.get(t, 0) + 1
        per_weight[w] = per_weight.get(w, 0) + 1
        per_ewt[popcount(wit)] = per_ewt.get(popcount(wit), 0) + 1
    print(json.dumps(dict(instance=meta_path, kills_verified=len(kills), per_level=per_level, per_weight=per_weight,
                          witness_e_weight=per_ewt)))

if __name__ == '__main__':
    main(*sys.argv[1:4], *(int(a) for a in sys.argv[4:5]))
