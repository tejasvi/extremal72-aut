import sys, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
from v4sat import group_elements, fpf_involution_classes
res=pickle.load(open('invs.pkl','rb'))
for key in ['3_6','25_2','15_2','20_7','23_2','21_2','0_0']:
    ci,ri=map(int,key.split('_'))
    G=group_elements(res[ci]['perms']); reps,_=fpf_involution_classes(G)
    bb=reps[ri]
    C=[g for g in G if all(g[bb[i]]==bb[g[i]] for i in range(36))]
    print(key,'|Aut(Y)|',len(G),'|C(bb)|',len(C),flush=True)
