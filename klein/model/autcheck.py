import sys, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
from autinv import load, span, rank, nauty_gens, apply
from v4sat import group_elements
codes=load(); classes=pickle.load(open('classes.pkl','rb'))
bad=0
for ci,G in enumerate(codes):
    W=span(G); Wset=set(W)
    w10=[w for w in W if bin(w).count('1')==10]
    assert rank(w10)==18
    perms,gs=nauty_gens(w10)
    perms=[p for p in perms if all(apply(p,g) in Wset for g in G)]
    order=len(group_elements(perms)) if perms else 1
    ref=classes[ci][1]
    flag='' if order==ref else '  MISMATCH'
    if flag: bad+=1
    print(ci, 'weight-10 graph:', gs, 'group from valid gens', order, 'vs', ref, flag, flush=True)
print('mismatches', bad)
