import glob, re, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
tot={}
for f in glob.glob('out/lw_*.out'):
    m=re.match(r'out/lw_(\d+_\d+)_(\d+)\.out',f); inst,p=m.group(1),int(m.group(2))
    txt=open(f).read()
    d=[l for l in txt.split('\n') if l.startswith('DONE lwe')]
    assert len(d)==1, f
    fl=d[0].split()
    nsol=int(fl[3]); t=int(fl[5].rstrip('s')); spl=int(fl[7]); part=fl[9]
    assert part==f"{p}/64" and spl==4, (f,d[0])
    nodes=sum(int(l.split()[7]) for l in txt.split('\n') if l.startswith('LEVEL'))
    a=tot.setdefault(inst,[0,0,0,0]); a[0]+=1; a[1]+=nsol; a[2]+=t; a[3]+=nodes
for k,v in sorted(tot.items()): print(f"{k}: parts {v[0]}/64, solutions {v[1]}, cpu {v[2]} s, nodes {v[3]:.3e}")
