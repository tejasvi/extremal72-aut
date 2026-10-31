"""patch_rc11.py SRC DST avx512|avx2 : rc11 = rc9 + optional LTSBFILE (bit-granular LTS, struct's prototype
struct/src/lwe10b.c, same decisions and counts).  lwe11b5 = lwe11b3 + the same.  The LB test runs after the LTSH
test, as in lwe10b's lh_reject; it is evaluated only for the comparands whose determined key prefix grew at level
t-1 (trigger lists), and LWE11CHECK compares it with the prototype's full loop at every node.  Without LTSBFILE the
only change is one predicted branch per node.  Exact anchors, each must occur once."""
import sys

src, dst, isa = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(src).read()


def rep(old, new):
    global s
    n = s.count(old)
    if n != 1:
        sys.exit(f"anchor found {n} times: {old[:80]!r}")
    s = s.replace(old, new)


NOTE = ("//    rc11: optional LTSBFILE (bit-granular LTS, struct's struct/src/lwe10b.c prototype): a comparand g whose\n"
        "//    transported key-word syndrome is not yet fully determined is compared MSB first on its determined leading\n"
        "//    bits; the node is pruned when that prefix is already smaller than s0.  Trigger lists per level; LWE11CHECK\n"
        "//    compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n")
if isa == 'avx512':
    rep("// lwe11 (c2opt/alg stream, 2026-10-21, release rc9) = lwe10 with a new level filter; same search tree, same pruning decisions,",
        "// lwe11 (c2opt/alg stream, 2026-10-21, release rc11) = lwe10 with a new level filter; same search tree, same pruning decisions,")
    rep("//    rc9: arena layout and dedicated loops also for kt = 11, 12 (four / eight ZMMs).\n",
        "//    rc9: arena layout and dedicated loops also for kt = 11, 12 (four / eight ZMMs).\n" + NOTE)
else:
    rep("// lwe11b (c2opt/alg stream, 2026-10-21) = the AVX2 build of lwe11 rc9: identical algorithm and tables; the translation of",
        "// lwe11b (c2opt/alg stream, 2026-10-21) = the AVX2 build of lwe11 rc11 (lwe11b5): identical algorithm and tables; the translation of")
    rep("// base bitmaps uses a 128-bit lane swap + VPSHUFB for bytes and nibble lookups for bits instead of VPERMB/GF2P8AFFINEQB.\n",
        "// base bitmaps uses a 128-bit lane swap + VPSHUFB for bytes and nibble lookups for bits instead of VPERMB/GF2P8AFFINEQB.\n"
        + NOTE.replace("//    rc11:", "// rc11:").replace("\n//    ", "\n// "))

LBBLOCK = r'''// rc11: bit-granular LTS (LTSBFILE written by struct's mkltsb.py / ltsblib.py; decisions as struct/src/lwe10b.c).
// File: 'LTSB nG m0 c0', then per g in G one line 'lv(c_u) F_0 c_0 L_0 ... F_{m0-1} c_{m0-1} L_{m0-1}': bit j of the
// transported key-word syndrome s_w0(B^g) is parity(F_j & x) ^ c_j, determined once all variables of levels <= L_j are
// assigned; lv(c_u) is the level of the constraint of u = g w0.  At a node of level t (> lv0), every g with
// lv(c_u) > t-1 is compared MSB first on its determined leading bits with s0 = s_w0(B); the node is pruned when that
// prefix is already smaller.  Then s_w0(B^g) < s0 for every completion, and since canon0 is the S0-orbit minimum
// (canon0(a) <= a) the LTSH test prunes every completion once c_u is complete: the leaf set does not change.
// A comparand whose determined prefix did not grow at level t-1 gives the same answer as at the parent (no prune), so
// level t only tests its trigger list LBtg[LBts[t] .. LBts[t+1]-1] (at t = lv0+1: every comparand with a prefix).
static int LB = 0, LBnG = 0, LBm0 = 0; static int *LBlu = NULL; static u128 *LBF = NULL; static unsigned char *LBc = NULL;
static signed char *LBlev = NULL; static long long lbprune[41], lbchecked = 0;
static int LBts[42], *LBtg = NULL; static unsigned char lbact[42];
static int lb_lvl(u128 v) {               // level of the highest variable of a form, -1 for 0, -2 if beyond the variables
    if (!v) return -1;
    const u64 hi = (u64)(v >> 64), lo = (u64)v; const int hb = hi ? 127 - __builtin_clzll(hi) : 63 - __builtin_clzll(lo);
    for (int t = 0; t < NLEV; t++) if (vstart[t] <= hb && hb < vstart[t + 1]) return t;
    return -2;
}
static void read_ltsb(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open ltsb");
    char tag[16]; int c0;
    if (fscanf(f, "%15s %d %d %d", tag, &LBnG, &LBm0, &c0) != 4 || strcmp(tag, "LTSB")) die("ltsb hdr");
    if (!LH || LBm0 != LHm0 || c0 != LHc0 || LBnG != LHnG) die("ltsb does not match the LTSH file");
    LBlu = malloc(sizeof(int) * LBnG); LBF = malloc(sizeof(u128) * (size_t)LBnG * LBm0);
    LBc = malloc((size_t)LBnG * LBm0); LBlev = malloc((size_t)LBnG * LBm0);
    if (!LBlu || !LBF || !LBc || !LBlev) die("alloc");
    for (int g = 0; g < LBnG; g++) {
        if (fscanf(f, "%d", &LBlu[g]) != 1 || LBlu[g] < 0 || LBlu[g] >= NLEV) die("ltsb lu");
        for (int j = 0; j < LBm0; j++) {
            char hx[64]; int c, l; if (fscanf(f, "%63s %d %d", hx, &c, &l) != 3) die("ltsb bit");
            u128 v = 0; for (char *q = hx; *q; q++) { int dv = (*q <= '9') ? *q - '0' : ((*q | 32) - 'a' + 10); v = (v << 4) | (u128)dv; }
            if ((c != 0 && c != 1) || l < -1 || l >= NLEV) die("ltsb bit value");
            if (lb_lvl(v) != l) die("ltsb: a bit's level differs from the level of its form's highest variable");
            size_t o = (size_t)g * LBm0 + j; LBF[o] = v; LBc[o] = (unsigned char)c; LBlev[o] = (signed char)l;
        }
    }
    fclose(f);
    for (int a = 0; a < (1 << LHm0); a++) if (LHcanon[a] > a) die("ltsb: canon0 is not the orbit minimum");
    LB = 1;
}
static int lb_plen(int g, int t) {         // leading (MSB-first) bits of comparand g determined at level t
    int p = 0; for (int j = LBm0 - 1; j >= 0 && LBlev[(size_t)g * LBm0 + j] <= t - 1; j--) p++; return p;
}
static void build_lb(void) {
    const int lv0 = C[LHc0].lv; int n = 0;
    LBtg = malloc(sizeof(int) * ((size_t)LBnG * (NLEV + 1) + 1)); if (!LBtg) die("alloc");
    for (int t = 0; t <= NLEV; t++) {
        LBts[t] = n; lbact[t] = 0;
        if (t - 1 < lv0 || t >= NLEV) continue;
        for (int g = 0; g < LBnG; g++) {
            if (LBlu[g] <= t - 1) continue;
            const int p = lb_plen(g, t), pp = (t == lv0 + 1) ? 0 : lb_plen(g, t - 1);
            if (p > pp) LBtg[n++] = g;
        }
        lbact[t] = (unsigned char)(n > LBts[t]);
    }
    LBts[NLEV + 1] = n;
}
static int lb_reject_full(int t) {         // struct/src/lwe10b.c's lb_reject (every comparand): LWE11CHECK reference
    int lv0 = C[LHc0].lv;
    if (t - 1 < lv0) return 0;
    int s0 = syn_ep(LHc0);
    for (int g = 0; g < LBnG; g++) {
        if (LBlu[g] <= t - 1) continue;
        for (int j = LBm0 - 1; j >= 0; j--) {
            size_t o = (size_t)g * LBm0 + j;
            if (LBlev[o] > t - 1) break;
            int b = par128(LBF[o] & asg) ^ LBc[o], sb = (s0 >> j) & 1;
            if (b < sb) return 1;
            if (b > sb) break;
        }
    }
    return 0;
}
static int lb_reject_fast(int t) {         // same decision as lb_reject_full, over the trigger list of level t
    const int s0 = syn_ep(LHc0);
    for (int q = LBts[t]; q < LBts[t + 1]; q++) {
        const int g = LBtg[q]; const size_t o0 = (size_t)g * LBm0;
        for (int j = LBm0 - 1; j >= 0; j--) {
            const size_t o = o0 + j;
            if (LBlev[o] > t - 1) break;
            const int b = par128(LBF[o] & asg) ^ LBc[o], sb = (s0 >> j) & 1;
            if (b < sb) return 1;
            if (b > sb) break;
        }
    }
    return 0;
}
static inline int syn_cached(int c) {
'''

rep("static inline int syn_cached(int c) {\n", LBBLOCK)

rep("    if (LH && lhact[t] && (LH2 ? lh_reject2(t) : lh_reject(t))) { lhprune[t]++; return; }\n"
    "    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }\n",
    "    if (LH && lhact[t] && (LH2 ? lh_reject2(t) : lh_reject(t))) { lhprune[t]++; return; }\n"
    "    if (LB) {                          // rc11: bit-granular comparands after the LTSH test (as lwe10b's lh_reject)\n"
    "        const int rb = lbact[t] ? lb_reject_fast(t) : 0;\n"
    "        if (CHECK) { const int rf = lb_reject_full(t); lbchecked++;\n"
    "            if (rf != rb) { fprintf(stderr, \"CHECK lb fast %d != full %d at level %d\\n\", rb, rf, t); exit(3); } }\n"
    "        if (rb) { lbprune[t]++; lhprune[t]++; return; }\n"
    "    }\n"
    "    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }\n")

rep('    { const char *hf = getenv("LTSHFILE"); if (hf) read_ltsh(hf); }\n',
    '    { const char *hf = getenv("LTSHFILE"); if (hf) read_ltsh(hf); }\n'
    '    { const char *bf = getenv("LTSBFILE"); if (bf) { read_ltsb(bf); build_lb(); } }\n')

rep('!(LH && lhact[SPL]) && !getenv("LWE11NOFASTSPLIT");',
    '!(LH && lhact[SPL]) && !(LB && lbact[SPL]) && !getenv("LWE11NOFASTSPLIT");')

rep('    printf("SYMPRUNE at leaves %lld LTSPRUNE at leaves %lld LHPRUNE at leaves %lld\\n", symprune[NLEV], ltsprune[NLEV], lhprune[NLEV]);\n',
    '    printf("SYMPRUNE at leaves %lld LTSPRUNE at leaves %lld LHPRUNE at leaves %lld\\n", symprune[NLEV], ltsprune[NLEV], lhprune[NLEV]);\n'
    '    if (LB) { printf("LBPRUNE"); for (int t = 0; t <= NLEV; t++) printf(" %d:%lld", t, lbprune[t]); printf("\\n"); }\n'
    '    if (CHECK && LB) fprintf(stderr, "LB check: %lld nodes compared with the full test\\n", lbchecked);\n')

rep('        if (CHECK && LH && lh_reject(t)) { fprintf(stderr, "CHECK fast split at level %d\\n", t); exit(3); }\n',
    '        if (CHECK && LH && lh_reject(t)) { fprintf(stderr, "CHECK fast split at level %d\\n", t); exit(3); }\n'
    '        if (CHECK && LB && lb_reject_full(t)) { fprintf(stderr, "CHECK fast split (LB) at level %d\\n", t); exit(3); }\n')

open(dst, 'w').write(s)
print("patched", src, "->", dst)
