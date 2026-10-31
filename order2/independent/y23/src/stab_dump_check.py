"""Depth-104 orbit test of the Stab(X) reduction (pure python3).
usage: stab_dump_check.py STAB_PKL FULL_DUMP RED_DUMP
FULL_DUMP / RED_DUMP: outputs of engine12 joinstabdump without / with the stab file (PP h h' lines and JT lines).
Per X (the JT line ends each X's block of PP lines):
  Pass = passing pairs of the unreduced run, R = those of the reduced run.
  Checks: R is a subset of Pass; every (h, h') in R is canonical (phi_g(h) >= h for all T-preserving g,
  psi_g(h') >= h for all swapping g); the Stab(X)-images of R, (phi_g h, phi'_g h') for T-preserving g and
  (psi_g h', psi'_g h) for swapping g, are exactly Pass; Pass is Stab(X)-invariant."""
import sys, pickle

store = pickle.load(open(sys.argv[1], "rb"))


def aff(m, h):
    c, cols = m
    y = c
    k = 0
    while h:
        if h & 1:
            y ^= cols[k]
        h >>= 1
        k += 1
    return y


def read_dump(fn):
    out, cur = {}, set()
    for l in open(fn):
        f = l.split()
        if not f:
            continue
        if f[0] == "PP":
            cur.add((int(f[1], 16), int(f[2], 16)))
        elif f[0] == "JT":
            x = int(f[1], 16)
            assert x not in out
            assert int(f[7]) == len(cur), "npass differs from the number of PP lines"
            out[x] = (cur, f)
            cur = set()
    assert not cur, "PP lines after the last JT line"
    return out


full, red = read_dump(sys.argv[2]), read_dump(sys.argv[3])
bad = 0
for x in sorted(full):
    Pass, ff = full[x]
    R, fr = red[x]
    S = store[x]
    phi, phi2, psi, psi2 = S["phi"], S["phi2"], S["psi"], S["psi2"]
    assert int(fr[14]) == len(phi) and int(fr[15]) == len(psi)
    sub = R <= Pass
    canon = all(all(aff(m, h) >= h for m in phi) and all(aff(m, h2) >= h for m in psi) for h, h2 in R)
    E = set()
    for h, h2 in R:
        for a, b in zip(phi, phi2):
            E.add((aff(a, h), aff(b, h2)))
        for a, b in zip(psi, psi2):
            E.add((aff(a, h2), aff(b, h)))
    inv = all((aff(a, h), aff(b, h2)) in Pass for h, h2 in Pass for a, b in zip(phi, phi2)) and \
        all((aff(a, h2), aff(b, h)) in Pass for h, h2 in Pass for a, b in zip(psi, psi2))
    ok = sub and canon and E == Pass and inv
    bad += not ok
    print("X %x |Stab| %d (pres %d, swap %d): |S1| %s kept %s |S2| %s | pairs full %s red %s | pass full %d red %d"
          " | subset %s canonical %s expansion==full %s invariant %s -> %s"
          % (x, len(phi) + len(psi), len(phi), len(psi), ff[3], fr[4], ff[5], ff[6], fr[6], len(Pass), len(R),
             sub, canon, E == Pass, inv, "OK" if ok else "FAIL"))
print("ALL OK" if bad == 0 else "FAILURES %d" % bad)
