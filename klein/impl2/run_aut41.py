import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import *
codes = json.load(open(HERE + '/data/codes41.json'))
out = []
for c in codes:
    B = c['basis']
    w, words = low_weight_words_spanning(B, 36)
    gens, gs, raw = dreadnaut_aut(36, words)
    assert all(is_aut(p, B, 36) for p in gens)
    print(c['idx'], 'span_w', w, 'nwords', len(words), 'grpsize', gs, 'ngens', len(gens), flush=True)
    out.append(dict(idx=c['idx'], span_w=w, grpsize=gs, gens=gens))
json.dump(out, open(HERE + '/data/aut41.json', 'w'))
