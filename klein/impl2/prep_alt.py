"""Alternative variable orders (second-best distinct schedule) for cross-check runs."""
import sys, json, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from instance import Instance
from order import *
from export import export

def prep(ci, cl, outdir=HERE + '/inst3'):
    codes = json.load(open(HERE + '/data/codes41.json'))
    fpf = json.load(open(HERE + '/data/fpf41.json'))
    prod = json.load(open(HERE + '/inst2/i72_c%02d_b%d.json' % (ci, cl)))
    beta = fpf[ci - 1]['classes'][cl]['beta']
    I = Instance(codes[ci - 1]['basis'], beta, 16)
    I.set_order(list(I.yb0))
    infos = reachable_info(I)
    G = CosetGreedy2(I, infos)
    I.set_order(list(I.yb0))
    F = fixed_space_basis(I); Im = image_space_basis(I)
    def allc(basis):
        cs = [I.coords(b) for b in basis]
        out = [0]
        for c in cs:
            out = out + [x ^ c for x in out]
        return out
    Fall = allc(F); Iall = allc(Im)
    scheds = [("F%d" % nf, [(Fall, nf)]) for nf in range(0, len(F) + 1)]
    scheds += [("I%d+F" % ni, [(Iall, ni), (Fall, len(F))]) for ni in range(1, len(Im) + 1)]
    res = []
    for name, sc in scheds:
        o = G.order_sched(sc)
        I.set_order(o)
        res.append((work_estimate2(I, infos), name, o, list(I.k_t)))
    res.sort(key=lambda r: r[0])
    for w, name, o, kt in res:
        if o != prod['order']:
            break
    I.set_order(o)
    path = "%s/i72_c%02d_b%d.txt" % (outdir, ci, cl)
    export(I, path)
    meta = dict(code=ci, cls=cl, N=I.N, k_t=I.k_t, ncons=len(I.cons), log2est=round(w, 2), sched=name, order=o, beta=beta,
                prod_sched=prod['sched'], prod_k_t=prod['k_t'])
    json.dump(meta, open(path.replace('.txt', '.json'), 'w'))
    print(json.dumps({k: v for k, v in meta.items() if k not in ('order', 'beta')}), flush=True)

if __name__ == '__main__':
    for a in sys.argv[1:]:
        ci, cl = map(int, a.split(':'))
        prep(ci, cl)
