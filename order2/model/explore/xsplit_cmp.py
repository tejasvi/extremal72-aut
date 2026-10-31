"""Independent check of fleet's SPLIT cross-checks (results/<pkg>/xcheck/split/p<k>/s<j>.log): production part k of
NPART is re-run as the M sub-parts k + NPART*j (j = 0..M-1) of M*NPART at the same split level (M read from the
first sub-part's DONE line; 16 for y40/y12-lb2, 32 for y15-lb), whose union is exactly
part k's subtrees (a split-level node with index i belongs to part i mod NPART).  Checks per part k:
  - every sub-part log: one DONE line naming part k + NPART*j of 16*NPART and the plan's split level, nsol 0, no STOPPED;
  - prefix (LEVEL lines of levels < SPL, the level-SPL line without kids, LBPRUNE entries <= SPL) equal to production;
  - sums over the 16 sub-parts equal the production part: kids at level SPL, nodes/kids/symprune/ltsprune/lhprune at
    every level > SPL, the leaf-prune line, LBPRUNE entries > SPL;
  - ORIGIN rows: reference engine lwe10 / lwe10b binary (frozen kits), measured exe = that binary, env not BAD, a CPU
    family other than the production part's box; SHA256SUMS verified.
Usage: xsplit_cmp.py PKG NPART SPL PART [PART ...]   prints one line per part and 'xcheck split N/M identical'."""
import os, re, sys, subprocess

pkg, npart, spl = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); parts = [int(x) for x in sys.argv[4:]]
R = os.environ.get('C2E_TEST_RESULTS', f'<HOME>/c72/fleet/results/{pkg}'); X = f'{R}/xcheck'   # override only for tests
REF = {'7766661c5c1ff70be51a9ac7b76e983b68241540b62b8f871b3935edde347893',   # lwe10b (rc11/rc13 kits)
       '246ceb0bbe72f7f18c541de59f5622cd75b0d2c19196e55fa1def17783ca77e1'}   # lwe10b (b5/b7 kits)
rL = re.compile(r'^LEVEL (\d+) kt (\d+) ncons (\d+) nodes (\d+) kids (\d+) symprune (\d+) ltsprune (\d+) lhprune (\d+)$')
rD = re.compile(r'^DONE lwe nsol (\d+) time \d+s split (-?\d+) part (\d+)/(\d+) N (\d+)$')
rS = re.compile(r'^SYMPRUNE at leaves (\d+) LTSPRUNE at leaves (\d+) LHPRUNE at leaves (\d+)$')


def parse(fn):
    L, D, S, B, bad = {}, [], [], None, []
    for line in open(fn).read().splitlines():
        if (m := rL.match(line)): L[int(m.group(1))] = [int(v) for v in m.groups()]
        elif (m := rD.match(line)): D.append([int(v) for v in m.groups()])
        elif (m := rS.match(line)): S.append([int(v) for v in m.groups()])
        elif line.startswith('LBPRUNE'): B = {int(a): int(b) for a, b in (x.split(':') for x in line.split()[1:])}
        elif line.startswith(('STOPPED', 'SOLUTION')): bad.append(line[:20])
    return L, D, S, B, bad


prod_box = {}
for l in open(f'{R}/ORIGIN.tsv'):
    c = l.rstrip('\n').split('\t')
    if len(c) >= 3 and not l.startswith('#'): prod_box[int(c[0].lstrip('p'))] = c[2].split('-')[0]
orig = {}
for l in open(f'{X}/ORIGIN.tsv'):
    c = l.rstrip('\n').split('\t')
    if c[0].startswith('split/'): orig[c[0]] = c
rc = subprocess.run(['sha256sum', '-c', '--quiet', 'SHA256SUMS'], cwd=X, capture_output=True, text=True).returncode
print(f'split xcheck SHA256SUMS: rc {rc}')
ok = 0
for k in parts:
    probs = []
    pl, pd, ps, pb, _ = parse(f'{R}/parts/p{k}.log')
    nlev = len(pl); sumL = {t: [0] * 5 for t in range(spl + 1, nlev)}; kidsS = 0; leaf = [0, 0, 0]; lbs = {}
    f0 = f'{X}/split/p{k}/s0.log'
    d0 = parse(f0)[1] if os.path.exists(f0) else []
    M = d0[0][3] // npart if d0 and d0[0][3] % npart == 0 else 0
    nsub = len([f for f in os.listdir(f'{X}/split/p{k}') if re.match(r'^s\d+\.log$', f)]) if os.path.isdir(f'{X}/split/p{k}') else 0
    if M < 2 or nsub != M: probs.append(f'sub-part count: {nsub} files, M from s0 = {M}')
    for j in range(max(M, 1)):
        f = f'{X}/split/p{k}/s{j}.log'
        if not os.path.exists(f): probs.append(f's{j} missing'); continue
        L, D, S, B, bad = parse(f)
        if bad or len(D) != 1 or D[0][0] != 0 or D[0][1] != spl or D[0][2] != k + npart * j or D[0][3] != M * npart:
            probs.append(f's{j} DONE/STOPPED/SOLUTION'); continue
        if sorted(L) != sorted(pl) or len(S) != 1: probs.append(f's{j} LEVEL lines'); continue
        if any(L[t] != pl[t] for t in range(spl)) or L[spl][:4] + L[spl][5:] != pl[spl][:4] + pl[spl][5:]:
            probs.append(f's{j} prefix differs')
        kidsS += L[spl][4]
        for t in range(spl + 1, nlev):
            for i, v in enumerate(L[t][3:8]): sumL[t][i] += v
        for i in range(3): leaf[i] += S[0][i]
        if (B is None) != (pb is None): probs.append(f's{j} LBPRUNE presence')
        elif B:
            if any(B[t] != pb[t] for t in range(spl + 1)): probs.append(f's{j} LB prefix differs')
            for t in B:
                if t > spl: lbs[t] = lbs.get(t, 0) + B[t]
        o = orig.get(f'split/p{k}/s{j}')
        if not o: probs.append(f's{j} no ORIGIN row')
        else:
            if o[4] not in REF: probs.append(f's{j} engine {o[3]} {o[4][:12]}')
            ex = [x for x in o if x.startswith('exe:')]; ev = [x for x in o if x.startswith('env:')]
            if ex and ex[0][4:] != o[4]: probs.append(f's{j} measured exe {ex[0][4:16]}')
            if ev and ev[0].startswith('env:BAD'): probs.append(f's{j} {ev[0]}')
            if o[2].split('-')[0] == prod_box.get(k): probs.append(f's{j} same family {o[2]}')
    if kidsS != pl[spl][4]: probs.append(f'kids at split level {kidsS} != {pl[spl][4]}')
    for t in range(spl + 1, nlev):
        if sumL[t] != pl[t][3:8]: probs.append(f'level {t} sums differ'); break
    if leaf != ps[0]: probs.append('leaf sums differ')
    if pb and any(lbs.get(t, 0) != pb[t] for t in pb if t > spl): probs.append('LBPRUNE sums differ')
    if rc: probs.append('SHA256SUMS')
    if not probs: ok += 1
    print(f'p{k}: ' + (f'IDENTICAL ({M} sub-parts sum to the production part)' if not probs else 'DIFFERENT ' + str(probs[:6])))
print(f'xcheck split {ok}/{len(parts)} identical')
