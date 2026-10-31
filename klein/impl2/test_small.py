"""Cross-check the C engine against brute force on small instances (length 32, d=8)."""
import sys, json, random, subprocess, itertools, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from instance import Instance
from order import best_order
from export import *
from autgroup import apply_perm_vec, is_aut
import numpy as np

def e8():
    rows = ["11110000", "00111100", "00001111", "01010101"]
    return [row_to_int([int(c) for c in r]) for r in rows]

def run_engine(path):
    out = subprocess.run([HERE + "/search", path], capture_output=True, text=True).stdout
    sols = []
    for line in out.splitlines():
        if line.startswith("SOL"):
            sols.append(tuple(int(t) for t in line.split()[1:]))
    return sols, out

def brute(I, dmin):
    sols = []
    N = I.N
    for xi in range(1 << N):
        x = [(xi >> s) & 1 for s in range(N)]
        G = gram_from_x(I, x)
        rows = build_code(I, G)
        wd = weight_distribution(rows, 2 * I.n2)
        d = min(i for i in range(1, 2 * I.n2 + 1) if wd[i])
        assert all(w % 4 == 0 for w in range(len(wd)) if wd[w]), "not doubly even"
        if d >= dmin:
            sols.append(tuple(x))
    return sols

def test(Ybasis, beta, dmin, name, seed=0, order='best'):
    I = Instance(Ybasis, beta, dmin, name)
    if order == 'best':
        best_order(I)
    else:
        random.seed(seed)
        # random basis order
        S = Span(); o = []
        cand = [int(v) for v in span_array(I.yb0)]
        random.shuffle(cand)
        for v in cand:
            if S.add(v): o.append(v)
        I.set_order(o)
    path = "/tmp/v4indep_test_%s.txt" % name
    export(I, path)
    t0 = time.time()
    es, out = run_engine(path)
    t1 = time.time()
    bs = brute(I, dmin)
    t2 = time.time()
    print(name, "N", I.N, "k_t", I.k_t, "engine", len(es), "brute", len(bs), "match", sorted(es) == sorted(bs),
          "times %.2f %.2f" % (t1 - t0, t2 - t1), flush=True)
    assert sorted(es) == sorted(bs)
    return len(es)

if __name__ == '__main__':
    E = e8()
    Y1 = E + [v << 8 for v in E]
    # beta 1: block swap
    b1 = [i + 8 if i < 8 else i - 8 for i in range(16)]
    # beta 2: translation x -> x + (1,0,0) in AG(3,2) labeling: e8 coordinates labelled so that 01010101 ... use pair swaps (0 1)(2 3)(4 5)(6 7)
    t = [1, 0, 3, 2, 5, 4, 7, 6]
    b2 = t + [x + 8 for x in t]
    # beta 3: (0 2)(1 3)(4 6)(5 7) in block 1, block swap composed? use t' on block 1, t on block 2
    t2 = [2, 3, 0, 1, 6, 7, 4, 5]
    b3 = t2 + [x + 8 for x in t]
    for nm, b in [("e8e8_swap", b1), ("e8e8_tt", b2), ("e8e8_t2t", b3)]:
        assert is_aut(b, Y1, 16), nm
        for o in ['best', 'rand']:
            for seed in range(2 if o == 'rand' else 1):
                test(Y1, b, 8, nm + "_" + o + str(seed), seed=seed, order=o)
    # d16+
    d16 = []
    for i in range(7):
        d16.append(sum(1 << j for j in range(2 * i, 2 * i + 4)))
    d16.append(sum(1 << j for j in range(1, 16, 2)))
    assert rank(d16) == 8 and all(dot(x, y) == 0 for x in d16 for y in d16)
    # fpf involutions of d16+: swap within each pair (2i,2i+1) -> fixes? maps 0101.. to 1010.. = glue + all-ones? check
    p1 = [i ^ 1 for i in range(16)]
    p2 = [15 - i for i in range(16)]
    p3 = [(i + 8) % 16 for i in range(16)]
    for nm, b in [("d16_pairswap", p1), ("d16_reverse", p2), ("d16_shift8", p3)]:
        if not is_aut(b, d16, 16):
            print(nm, "not an automorphism; skipped"); continue
        for o in ['best', 'rand']:
            test(d16, b, 8, nm + "_" + o, seed=5, order=o)
    print("ALL SMALL TESTS PASSED")
