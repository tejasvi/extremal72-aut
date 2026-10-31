"""variant of mkpar for the w10 count only: g = sum_{y in Y10} a_1(Q_y) mod 2, expected 0"""
import sys, subprocess
sys.argv = [sys.argv[0], sys.argv[1], 'x10', sys.argv[2], '0']
src = open('<HOME>/c72/c2opt/math/mkpar.py').read()
src = src.replace("""        if kind == 'x8' and j != 8:
            continue""", """        if kind == 'x8' and j != 8:
            continue
        if kind == 'x10' and j != 10:
            continue""")
src = src.replace("""            elif kind == 'x8':
                v = 1 if 0 in ss else 0""", """            elif kind == 'x8':
                v = 1 if 0 in ss else 0
            elif kind == 'x10':
                v = len(ss) % 2""")
exec(compile(src, 'mkpar_x10', 'exec'))
