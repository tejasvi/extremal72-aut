import os, re, glob
os.chdir(os.path.dirname(os.path.abspath(__file__)))
old=set()
for l in open('wide_status.txt'):
    t,i,p=l.split()
    if t=='OLD': old.add((i,int(p)))
insts=sorted(set(re.sub(r'v4_(\d+_\d+)\.txt(\.gz)?',r'\1',os.path.basename(f)) for f in glob.glob('inst/v4_*.txt*')))
def done(f):
    try:
        for l in open(f):
            if l.startswith('DONE result=COMPLETE'): return l
    except FileNotFoundError: return None
    return None
def sols(f):
    try: return sum(1 for l in open(f) if l.startswith('SOLUTION') or l.startswith('LEAF'))
    except FileNotFoundError: return 0
tot_nodes=0; incomplete={}; nsol=0
for i in insts:
    if i=='0_0':
        parts=[done(f'test/w14_{p}.out') for p in range(64)]
        nsol+=sum(sols(f'test/w14_{p}.out') for p in range(64))
        if all(parts): tot_nodes+=sum(int(x.split()[3]) for x in parts)
        else: incomplete[i]=[p for p in range(64) if not parts[p]]
        continue
    miss=[]
    for p in range(16):
        f=f'out2/v4_{i}_{p}.out' if (i,p) in old else f'out/v4_{i}_{p}.out'
        d=done(f); nsol+=sols(f)
        if d: tot_nodes+=int(d.split()[3])
        else: miss.append(p)
    if miss: incomplete[i]=miss
print("instances",len(insts),"fully complete",len(insts)-len(incomplete),"solutions/leaves",nsol,"nodes in complete parts",tot_nodes)
for i,m in sorted(incomplete.items()): print("INCOMPLETE",i,m)
