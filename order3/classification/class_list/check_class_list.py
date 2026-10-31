#!/usr/bin/env python3
"""Check the class list cls24.txt.gz and recompute its summary numbers.

Usage: python3 check_class_list.py cls24.txt.gz

Reads the gzip stream once. Checks that every line has the form
  KEY AUT A8 SC IDX
with KEY = 192 lower-case hex digits, AUT, A8, IDX decimal integers, SC in {0, 1},
that the keys are strictly increasing, that A8 is divisible by 9, and that IDX < 45775.
Prints the sha256 of the decompressed list, the number of lines, the number of
classes up to monomial equivalence (lines with SC = 1 count once, SC = 0 twice),
the number of self-conjugate lines, and the histograms of beta = A8/9 and of AUT
(classes up to monomial equivalence and conjugation, as in Table 2 of the paper).
Exit status 1 if any check fails.
"""
import collections, gzip, hashlib, re, sys

LINE = re.compile(rb'([0-9a-f]{192}) ([0-9]+) ([0-9]+) ([01]) ([0-9]+)\n')

def main():
    h = hashlib.sha256()
    n = sc1 = mon = bad = 0
    prev = b''
    beta = collections.Counter()
    aut = collections.Counter()
    with gzip.open(sys.argv[1], 'rb') as f:
        for line in f:
            h.update(line)
            n += 1
            m = LINE.fullmatch(line)
            if not m:
                bad += 1
                if bad <= 5:
                    print('malformed line', n)
                continue
            key, a, a8, sc, idx = m.groups()
            if key <= prev:
                bad += 1
                if bad <= 5:
                    print('key order violated at line', n)
            prev = key
            a8 = int(a8)
            if a8 % 9 or int(idx) >= 45775:
                bad += 1
                if bad <= 5:
                    print('field check failed at line', n)
            beta[a8 // 9] += 1
            aut[int(a)] += 1
            if sc == b'1':
                sc1 += 1
                mon += 1
            else:
                mon += 2
    print('sha256 of decompressed list:', h.hexdigest())
    print('lines (classes up to monomial equivalence and conjugation):', n)
    print('classes up to monomial equivalence:', mon)
    print('self-conjugate lines:', sc1)
    print('malformed or failing lines:', bad)
    print('beta histogram (beta count):')
    for b in sorted(beta):
        print('  beta', b, beta[b])
    print('|Aut_Mon| histogram (order count):')
    for a in sorted(aut):
        print('  aut', a, aut[a])
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
