"""Prepare a C2 instance for a split run (frozen tools in this directory).
Usage: prep_code.py CI FLAGFILE KEYSPEC OUTDIR      KEYSPEC = 'flag:R' or 'words:w1,w2,...'
Writes OUTDIR/{flag.txt,key.txt,inst.txt,inst.txt.meta,inst.txt.pkl,sym.ltsh} and OUTDIR/INPUTS.sha256."""
import sys, os, pickle, hashlib, subprocess
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from common import load
import mkinst
from symprep3 import prep3
ci = int(sys.argv[1]); flagf = sys.argv[2]; keyspec = sys.argv[3]; out = sys.argv[4]
os.makedirs(out, exist_ok=True)
flag = [int(x) for x in [l for l in open(flagf) if l.startswith('FLAG')][0].split()[1:]]
if keyspec.startswith('flag:'): key = flag[:int(keyspec[5:])]
else: key = [int(x) for x in keyspec[6:].split(',')]
open(os.path.join(out, 'flag.txt'), 'w').write('FLAG ' + ' '.join(map(str, flag)) + '\n')
open(os.path.join(out, 'key.txt'), 'w').write('KEY ' + ' '.join(map(str, key)) + '\n')
codes = load()
L = mkinst.build(codes[ci], flag)
inst = os.path.join(out, 'inst.txt')
mkinst.export(L, inst)
pickle.dump(dict(w=L['w'], free=L['free'], entf=L['entf'], N=L['N'], E=L['E']), open(inst + '.pkl', 'wb'))
res = pickle.load(open(os.path.join(here, 'invs.pkl'), 'rb'))
prep3(res[ci]['perms'], 36, inst, os.path.join(out, 'sym.ltsh'), flag, len(key), key=key)
files = ['flag.txt', 'key.txt', 'inst.txt', 'inst.txt.meta', 'inst.txt.pkl', 'sym.ltsh']
with open(os.path.join(out, 'INPUTS.sha256'), 'w') as f:
    for fn in files: f.write(hashlib.sha256(open(os.path.join(out, fn), 'rb').read()).hexdigest() + '  ' + fn + '\n')
    for fn in ['lwe8.c', 'mkinst.py', 'common.py', 'symprep.py', 'symprep2.py', 'symprep3.py', 'prep_code.py', 'codes36.txt', 'invs.pkl']:
        f.write(hashlib.sha256(open(os.path.join(here, fn), 'rb').read()).hexdigest() + '  frozen/' + fn + '\n')
print(open(os.path.join(out, 'INPUTS.sha256')).read())
