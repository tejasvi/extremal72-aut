import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
exec(open(HERE + '/control48v4.py').read().split("st, model = solve(S, timeout=1800)")[0])
from v4export import export
export(S,HERE + '/inst/qr48.txt')
print("exported")
