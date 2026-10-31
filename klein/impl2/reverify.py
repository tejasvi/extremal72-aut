"""Re-run verify_kills.py over existing KILL logs to collect per-weight statistics."""
import sys, subprocess, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
D = HERE
prefix = sys.argv[1]  # 'w2' or 'cert'
for name in sys.argv[2:]:
    out = '%s/logs/%s_%s.out' % (D, prefix, name)
    r = subprocess.run(['nice', '-n', '10', sys.executable, '-I', D + '/verify_kills.py',
                        D + '/inst2/%s.json' % name, D + '/inst2/%s.txt' % name, out], capture_output=True, text=True)
    if r.returncode == 0:
        res = json.loads(r.stdout.strip().splitlines()[-1]); res['name'] = name; res['src'] = prefix
        print(json.dumps(res), flush=True)
    else:
        print(json.dumps(dict(name=name, src=prefix, FAIL=r.stderr[-1000:])), flush=True)
