"""Complete kill certificates for small instances: every killed child is verified with an explicit witness;
the number of verified kills must equal the engine's total kill count."""
import sys, json, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from summarize import parse
D = HERE
for name in sys.argv[1:]:
    env = dict(os.environ, V4_WITNESS='1', V4_WITNESS_MAX='100000000')
    out = D + '/logs/cert_%s.out' % name
    with open(out, 'w') as fo:
        subprocess.run(['nice', '-n', '10', D + '/search_v4', D + '/inst2/%s.txt' % name], stdout=fo,
                       stderr=subprocess.DEVNULL, env=env, check=True)
    st = parse(open(out).read())
    nk = sum(1 for l in open(out) if l.startswith('KILL'))
    r = subprocess.run(['nice', '-n', '10', sys.executable, '-I', D + '/verify_kills.py',
                        D + '/inst2/%s.json' % name, D + '/inst2/%s.txt' % name, out], capture_output=True, text=True)
    ok = r.returncode == 0
    res = json.loads(r.stdout.strip().splitlines()[-1]) if ok else None
    complete = ok and st['nsol'] == 0 and nk == st['kills'] and res['kills_verified'] == nk
    print(json.dumps(dict(name=name, engine_kills=st['kills'], kill_lines=nk, verified=(res or {}).get('kills_verified'),
                          nsol=st['nsol'], complete_certificate=complete, err=None if ok else r.stderr[-500:])), flush=True)
