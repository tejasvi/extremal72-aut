"""Run engine in witness mode for each instance and verify sampled kills independently."""
import sys, json, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
D = HERE
summ = json.load(open(D + '/results/p1_summary.json'))
names = sys.argv[1:]
for name in names:
    s = summ.get('p1_%s.out' % name)
    extra = []
    if s is None:
        # hard instance: sample within one split job
        extra = ['64', '0', '9']
        M = 200003
    else:
        M = max(1, s['kills'] // 300)
    env = dict(os.environ, V4_WITNESS=str(M), V4_WITNESS_MAX='60')
    out = D + '/logs/w2_%s.out' % name
    with open(out, 'w') as fo:
        subprocess.run(['nice', '-n', '10', D + '/search_v4', D + '/inst2/%s.txt' % name] + extra, stdout=fo,
                       stderr=subprocess.DEVNULL, env=env, check=True)
    r = subprocess.run(['nice', '-n', '10', sys.executable, '-I', D + '/verify_kills.py',
                        D + '/inst2/%s.json' % name, D + '/inst2/%s.txt' % name, out], capture_output=True, text=True)
    res = r.stdout.strip().splitlines()[-1] if r.returncode == 0 else ('FAIL ' + r.stderr[-2000:])
    print(name, M, res, flush=True)
