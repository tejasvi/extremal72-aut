"""Prepare engine input files for all length-72 instances (code idx, class idx)."""
import sys, json, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from instance import Instance
from order import best_order
from export import export

def prep(ci, cl):
    codes = json.load(open(HERE + '/data/codes41.json'))
    fpf = json.load(open(HERE + '/data/fpf41.json'))
    c = codes[ci - 1]; f = fpf[ci - 1]
    assert c['idx'] == ci and f['idx'] == ci
    beta = f['classes'][cl]['beta']
    t0 = time.time()
    I = Instance(c['basis'], beta, 16, "c%02d_b%d" % (ci, cl))
    o, w, nf = best_order(I)
    path = HERE + "/inst/i72_c%02d_b%d.txt" % (ci, cl)
    export(I, path)
    meta = dict(code=ci, cls=cl, N=I.N, k_t=I.k_t, ncons=len(I.cons), log2est=round(w, 2), nfirst=nf,
                order=o, beta=beta, secs=round(time.time() - t0, 1))
    json.dump(meta, open(path.replace('.txt', '.json'), 'w'))
    print(json.dumps({k: v for k, v in meta.items() if k not in ('order', 'beta')}), flush=True)

if __name__ == '__main__':
    for a in sys.argv[1:]:
        ci, cl = map(int, a.split(':'))
        prep(ci, cl)
