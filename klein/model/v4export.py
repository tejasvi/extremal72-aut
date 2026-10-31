"""Export a C2xC2 instance for the C guess-and-determine solver.
Format (text): nW nwords; then per word: wt d ngood ; d lines 'mask_hex const' ; then good classes (ints) on one line."""
import sys, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
from v4sat import setup, group_elements, fpf_involution_classes, pc
from autinv import load
def export(S, fn):
    out=[]
    recs=sorted(S['recs'], key=lambda r: pc(r[0]))
    out.append(f"{S['nW']} {len(recs)}")
    for (y,sbc,bits,bad) in recs:
        d=len(sbc)
        good=[g for g in range(1<<d) if g not in bad]
        out.append(f"{pc(y)} {d} {len(good)}")
        for (vs,c) in bits:
            l=0
            for v_ in vs: l|=1<<(v_-1)
            out.append(f"{l:x} {c}")
        out.append(' '.join(map(str,good)))
    open(fn,'w').write('\n'.join(out)+'\n')
if __name__=='__main__':
    codes=load(); res=pickle.load(open(HERE + '/invs.pkl','rb'))
    import os
    os.makedirs(HERE + '/inst',exist_ok=True)
    which=[int(x) for x in sys.argv[1].split(',')] if len(sys.argv)>1 else range(41)
    for ci in which:
        G=group_elements(res[ci]['perms']); reps,_=fpf_involution_classes(G)
        for ri,bb in enumerate(reps):
            fn=f'{HERE}/inst/v4_{ci}_{ri}.txt'
            if os.path.exists(fn): continue
            S=setup(codes[ci],bb,verbose=False)
            export(S,fn)
            print(ci,ri,S['nW'],len(S['recs']),flush=True)
