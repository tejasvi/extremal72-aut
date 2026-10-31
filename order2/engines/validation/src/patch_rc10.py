"""patch_rc10.py SRC DST avx512|avx2 : rc10 = rc9 + optional LAWFILE (one F2-linear equation <l, x> = c over the engine
variables that every solution satisfies, e.g. math's A_12 parity law).  Children of the level that holds the last
support variable are pruned before the symmetry tests when they violate it.  LAWCOUNT=1 prunes nothing and reports
the counts made inside violating subtrees, so the pruned run can be compared line by line.  Without LAWFILE nothing
changes (the hot loop is untouched; one extra branch per kids_loop_p call).  Exact anchors, each must occur once."""
import sys

src, dst, isa = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(src).read()


def rep(old, new):
    global s
    n = s.count(old)
    if n != 1:
        sys.exit(f"anchor found {n} times: {old[:80]!r}")
    s = s.replace(old, new)


if isa == 'avx512':
    rep("// lwe11 (c2opt/alg stream, 2026-10-21, release rc9) = lwe10 with a new level filter; same search tree, same pruning decisions,",
        "// lwe11 (c2opt/alg stream, 2026-10-21, release rc10) = lwe10 with a new level filter; same search tree, same pruning decisions,")
    rep("//    rc9: arena layout and dedicated loops also for kt = 11, 12 (four / eight ZMMs).\n",
        "//    rc9: arena layout and dedicated loops also for kt = 11, 12 (four / eight ZMMs).\n"
        "//    rc10: optional LAWFILE, one F2-linear equation <l, x> = c that every solution satisfies (math's A_12 parity\n"
        "//    law); children violating it are pruned at the level of its last variable.  Without LAWFILE nothing changes.\n")
else:
    rep("// lwe11b (c2opt/alg stream, 2026-10-21) = the AVX2 build of lwe11 rc9: identical algorithm and tables; the translation of",
        "// lwe11b (c2opt/alg stream, 2026-10-21) = the AVX2 build of lwe11 rc10: identical algorithm and tables; the translation of")
    rep("// base bitmaps uses a 128-bit lane swap + VPSHUFB for bytes and nibble lookups for bits instead of VPERMB/GF2P8AFFINEQB.\n",
        "// base bitmaps uses a 128-bit lane swap + VPSHUFB for bytes and nibble lookups for bits instead of VPERMB/GF2P8AFFINEQB.\n"
        "// rc10: optional LAWFILE, one F2-linear equation <l, x> = c that every solution satisfies (math's A_12 parity law);\n"
        "// children violating it are pruned at the level of its last variable.  Without LAWFILE nothing changes.\n")

LAWBLOCK = r'''// rc10: LAWFILE = one equation <l, x> = c (mod 2) over the engine variables that every solution satisfies.  Lines:
// "N <N>" (must equal the instance's N), "C <0|1>", "L <variable indices>" (bit positions of the inst.txt form masks;
// several L lines accumulate); other lines (LAW, FLAG, INST, '#') are for the scripts.  At level LAWLV, the level of the
// last support variable, children with <l, x> != c are removed before the symmetry tests (counted in lawpruned).
// LAWCOUNT=1 removes nothing: counts made inside the subtree of a violating child are summed in b*[], and LAWOK lines
// print the totals minus those, i.e. what the pruned run must print when LAWLV >= the split level.
static int LAW = 0, LAWCOUNT = 0, LAWLV = 0, LAWC = 0, LAWK = 0; static int LAWIDX[128];
static u128 LAWLOW = 0; static u64 *LAWPAR[2], *LAWBUF; static long long lawpruned = 0, lawchecked = 0;
static long long bnodes[41], bkids[41], bsym[41], blts[41], blh[41], bsol = 0;
static void read_law(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open LAWFILE");
    char line[16384]; int haveN = 0, haveC = 0; u128 l = 0;
    while (fgets(line, sizeof line, f)) {
        char *p = line; while (*p == ' ' || *p == '\t') p++;
        if (p[0] == 'N' && (p[1] == ' ' || p[1] == '\t')) { if (atoi(p + 1) != N) die("LAWFILE: N differs from the instance"); haveN = 1; }
        else if (p[0] == 'C' && (p[1] == ' ' || p[1] == '\t')) { char *e; long c = strtol(p + 1, &e, 10); if (e == p + 1 || (c != 0 && c != 1)) die("LAWFILE: C must be 0 or 1"); LAWC = (int)c; haveC = 1; }
        else if (p[0] == 'L' && (p[1] == ' ' || p[1] == '\t')) {
            char *q = p + 1, *e;
            for (;;) {
                long v = strtol(q, &e, 10); if (e == q) break; q = e;
                if (v < 0 || v >= N) die("LAWFILE: variable index out of range");
                if ((l >> v) & 1) die("LAWFILE: repeated variable index");
                l |= ((u128)1) << v; LAWIDX[LAWK++] = (int)v;
            }
            while (*q == ' ' || *q == '\t' || *q == '\n' || *q == '\r') q++;
            if (*q) die("LAWFILE: bad L line");
        }
    }
    fclose(f);
    if (!haveN || !haveC) die("LAWFILE needs N and C lines");
    LAWLV = 0; for (int t = 0; t < NLEV; t++) if (l >> vstart[t]) LAWLV = t;
    const int kt = vstart[LAWLV + 1] - vstart[LAWLV]; const long nch = 1L << kt; const int nw = (int)((nch + 63) / 64);
    const u64 m = (u64)((l >> vstart[LAWLV]) & ((((u128)1) << kt) - 1));
    LAWLOW = l & ((((u128)1) << vstart[LAWLV]) - 1);
    for (int b = 0; b < 2; b++) LAWPAR[b] = calloc(nw + 1, sizeof(u64));
    LAWBUF = calloc(nw + 1, sizeof(u64));
    if (!LAWPAR[0] || !LAWPAR[1] || !LAWBUF) die("alloc");
    for (long v = 0; v < nch; v++) LAWPAR[__builtin_popcountll((u64)v & m) & 1][v >> 6] |= 1ULL << (v & 63);
    LAW = 1;
}
static void law_check(int t, const u64 *w, const u64 *wl, int nwords, u128 clearmask) {   // LWE11CHECK: law bit per child, directly
    for (int i = 0; i < nwords; i++) { u64 b = w[i]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; long v = ((long)i << 6) + j;
        u128 a = (asg & clearmask) | (((u128)v) << vstart[t]); int par = 0;
        for (int k = 0; k < LAWK; k++) par ^= (int)((a >> LAWIDX[k]) & 1);
        if ((par == LAWC) != (int)((wl[i] >> j) & 1)) { fprintf(stderr, "CHECK law mismatch at level %d child %ld\n", t, v); exit(3); }
        lawchecked++; } }
}
static void kids_loop_lawcount(int t, const u64 *w, int nwords, const u64 *P, const u64 *T, const u64 *M, u128 clearmask) {
    // LAWCOUNT: the loop of kids_loop_p, child by child; for a violating child the counts made in its subtree go to b*[]
    const int fs = fsplit_ok && t + 1 == SPL;
    long long s_nodes[40], s_kids[40], s_sym[40], s_lts[41], s_lh[41], s_sol = 0;
    for (int i = 0; i < nwords; i++) {
        u64 bits = w[i];
        while (bits) {
            int j = __builtin_ctzll(bits); bits &= bits - 1;
            long v = ((long)i << 6) + j;
            const int bad = !((M[i] >> j) & 1);
            if (bad) { memcpy(s_nodes, nodes, sizeof s_nodes); memcpy(s_kids, kids, sizeof s_kids); memcpy(s_sym, symprune, sizeof s_sym);
                       memcpy(s_lts, ltsprune, sizeof s_lts); memcpy(s_lh, lhprune, sizeof s_lh); s_sol = nsol; }
            kids[t]++;
            if (P && ((P[i] >> j) & 1)) {      // rejected in bulk: search(t+1) would count the node and lh-prune it
                if (CHECK && !stopflag) { asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v; nid[t + 1] = ++NIDC;
                    if (!lh_reject(t + 1)) { fprintf(stderr, "CHECK bulk LTSH mismatch level %d\n", t + 1); exit(3); } }
                nodes[t + 1]++; if (!stopflag) lhprune[t + 1]++;
                goto done;
            }
            if (fs && !stopflag) {             // search(t+1) would count the node, find no symmetry test and stop at the split
                nodes[t + 1]++; long long id = splitcnt++;
                if (id % NPART != PART) goto done;
                presplit = 1;
            }
            asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v;
            newdone[t + 1] = (unsigned char)(T && !((T[i] >> j) & 1));
            search(t + 1);
            newdone[t + 1] = 0; SETLEV(t);
        done:
            if (bad) { for (int q = 0; q < 40; q++) { bnodes[q] += nodes[q] - s_nodes[q]; bkids[q] += kids[q] - s_kids[q]; bsym[q] += symprune[q] - s_sym[q]; }
                       for (int q = 0; q < 41; q++) { blts[q] += ltsprune[q] - s_lts[q]; blh[q] += lhprune[q] - s_lh[q]; }
                       bsol += nsol - s_sol; }
        }
    }
    asg &= clearmask;
}
static void kids_loop_p(int t, const u64 *w, int nwords, const u64 *P, const u64 *T) {
    u128 clearmask = ~(((((u128)1) << (vstart[t + 1] - vstart[t])) - 1) << vstart[t]);
    if (LAW && t == LAWLV) {
        const u64 *M = LAWPAR[LAWC ^ par128(asg & LAWLOW)];   // children whose own support bits complete <l, x> = c
        if (LAWCOUNT && !probe_mode) { kids_loop_lawcount(t, w, nwords, P, T, M, clearmask); return; }
        if (!LAWCOUNT) {
            long long np = 0;
            for (int i = 0; i < nwords; i++) { np += __builtin_popcountll(w[i] & ~M[i]); LAWBUF[i] = w[i] & M[i]; }
            if (CHECK && !probe_mode) law_check(t, w, LAWBUF, nwords, clearmask);
            if (!probe_mode) lawpruned += np;
            w = LAWBUF;
        }
    }
'''

rep("static void kids_loop_p(int t, const u64 *w, int nwords, const u64 *P, const u64 *T) {\n"
    "    u128 clearmask = ~(((((u128)1) << (vstart[t + 1] - vstart[t])) - 1) << vstart[t]);\n",
    LAWBLOCK)

rep('    { const char *hf = getenv("LTSHFILE"); if (hf) read_ltsh(hf); }\n',
    '    { const char *hf = getenv("LTSHFILE"); if (hf) read_ltsh(hf); }\n'
    '    { const char *lw = getenv("LAWFILE"); if (lw) read_law(lw); LAWCOUNT = LAW && getenv("LAWCOUNT") != NULL; }\n')

rep('    printf("SYMPRUNE at leaves %lld LTSPRUNE at leaves %lld LHPRUNE at leaves %lld\\n", symprune[NLEV], ltsprune[NLEV], lhprune[NLEV]);\n',
    '    printf("SYMPRUNE at leaves %lld LTSPRUNE at leaves %lld LHPRUNE at leaves %lld\\n", symprune[NLEV], ltsprune[NLEV], lhprune[NLEV]);\n'
    '    if (LAW) {\n'
    '        printf("LAW level %d support %d c %d %s %lld\\n", LAWLV, LAWK, LAWC, LAWCOUNT ? "violating" : "pruned", LAWCOUNT ? bkids[LAWLV] : lawpruned);\n'
    '        if (LAWCOUNT) {\n'
    '            for (int t = 0; t < NLEV; t++) printf("LAWOK LEVEL %d kt %d ncons %d nodes %lld kids %lld symprune %lld ltsprune %lld lhprune %lld\\n", t, vstart[t + 1] - vstart[t], lstart[t + 1] - lstart[t], nodes[t] - bnodes[t], kids[t] - bkids[t], symprune[t] - bsym[t], ltsprune[t] - blts[t], lhprune[t] - blh[t]);\n'
    '            printf("LAWOK SYMPRUNE at leaves %lld LTSPRUNE at leaves %lld LHPRUNE at leaves %lld nsol %lld\\n", symprune[NLEV] - bsym[NLEV], ltsprune[NLEV] - blts[NLEV], lhprune[NLEV] - blh[NLEV], nsol - bsol);\n'
    '        }\n'
    '        if (CHECK) fprintf(stderr, "LAW check: %lld children verified\\n", lawchecked);\n'
    '    }\n')

open(dst, 'w').write(s)
print("patched", src, "->", dst)
