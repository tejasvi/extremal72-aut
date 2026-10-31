import sys, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
from v4sat import group_elements, fpf_involution_classes
res=pickle.load(open(HERE + '/invs.pkl','rb'))
tot=0; out=[]
for ci in range(41):
    G=group_elements(res[ci]['perms']); reps,n=fpf_involution_classes(G)
    out.append((ci,len(G),n,len(reps))); tot+=len(reps)
    print(ci,len(G),n,len(reps),flush=True)
print("total classes",tot)
pickle.dump(out,open(HERE + '/classes.pkl','wb'))
