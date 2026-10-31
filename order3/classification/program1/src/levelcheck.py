"""Exact level-by-level double count for the E_B classification:
sum_{C' at level k+1} (4^{k+1}-1)/3 / |Aut(C')|  ==  sum_{C at level k} ext(C) / |Aut(C)|   (Mon classes; 'x2' = 2 classes)
Usage: levelcheck.py prefix kmax   (files prefix.L{k}.txt and prefix.ext{k}.txt for k < kmax)"""
import sys
from fractions import Fraction
def parse_aut(s):
    two = s.endswith('x2'); return int(s.replace('x2', '')), (2 if two else 1)
pre, kmax = sys.argv[1], int(sys.argv[2])
allok = True
for k in range(1, kmax):
    rhs = Fraction(0)
    for line in open(f'{pre}.ext{k}.txt'):
        idx, ext, autstr = line.split(); a, m = parse_aut(autstr); rhs += m * Fraction(int(ext), a)
    lhs = Fraction(0); n = 0
    hyp = (4 ** (k + 1) - 1) // 3
    for line in open(f'{pre}.L{k+1}.txt'):
        p = line.split(); a, m = parse_aut(p[2]); lhs += m * Fraction(hyp, a); n += 1
    ok = (lhs == rhs); allok &= ok
    print(f"{pre}: level {k}->{k+1}: sum_ext/|Aut| = {float(rhs):.10g}, sum_hyp/|Aut(L{k+1})| = {float(lhs):.10g} over {n} classes: {'EQUAL' if ok else 'DIFFERENT'}")
print("ALL EQUAL" if allok else "MISMATCH")
