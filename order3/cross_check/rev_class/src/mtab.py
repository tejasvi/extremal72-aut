# replicate frames.c setup_Mtab for d=8, K=6 and tabulate M over all 4^6 classes
from collections import Counter
d=8; K=6; cnt=Counter()
for c in range(4**K):
    n=[0]*4; s=0
    for i in range(K):
        u=(c>>(2*i))&3; n[u]+=1; s^=u
    n[0]+=d-1-K; n[s]+=1
    cnt[max(n)]+=1
print(sorted(cnt.items()))
