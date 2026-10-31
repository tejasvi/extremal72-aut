"""patch_rc13.py SRC DST avx512|avx2 : rc13 = rc11 with less per-node overhead, same decisions and output.
 1. search_fast's wide multi-ZMM path (kt >= 10 without arena, kt > 12) moves into its own function, so search_fast's
    frame drops from ~17 KB to a few hundred bytes (no stack-clash probe loop at every node).
 2. kids_loop_b / bulk_mask use per-level static buffers for P, T and the bulk accumulators instead of ~32 KB of
    stack per call (no probe loop at every node with children).  A level's buffers are only in use while that level's
    kids loop runs, and recursion only goes deeper.
 3. The bit-granular test caches each transported bit per epoch: bit (g, j) depends only on variables of levels
    <= L_j, so its value is fixed while nid[L_j + 1] is unchanged.  LWE11CHECK still compares the fast test with the
    uncached full loop.  Each comparand g that compared greater is also cached with the deepest level dl its decision
    read (s0 and the bits used); while nid[dl + 1] is unchanged (dl + 1 <= t) the decision stands.
 4. kt = 10 (two ZMM halves): once one half of the children bitmap is all dead, the remaining translate lanes only
    load, permute and transform the live half.
 5. Child fusion: at a level with no node test (no LTSH/LTSB test there, not the split level, fast filter on, not the
    leaf level, no LWE11CHECK) the parent's kids loop stamps and counts the child and calls the filter directly instead
    of search(t + 1) with its tests that cannot fire.  Same counts and output.
Exact anchors, each must occur once."""
import sys

src, dst, isa = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(src).read()


def rep(old, new, cnt=1):
    global s
    n = s.count(old)
    if n != cnt:
        sys.exit(f"anchor found {n} times (want {cnt}): {old[:90]!r}")
    s = s.replace(old, new)


NOTE = ("//    rc13: less per-node overhead, same decisions: the wide filter path in its own function and per-level static\n"
        "//    buffers for the bulk masks (no 17-32 KB stack frames per node), bit-granular test bits and decisions cached\n"
        "//    per epoch, and at kt = 10 a half of the bitmap that is all dead is no longer translated.\n")
if isa == 'avx512':
    rep("// lwe11 (c2opt/alg stream, 2026-10-21, release rc11) = lwe10 with a new level filter; same search tree, same pruning decisions,",
        "// lwe11 (c2opt/alg stream, 2026-10-22, release rc13) = lwe10 with a new level filter; same search tree, same pruning decisions,")
    rep("//    compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n",
        "//    compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n" + NOTE)
else:
    rep("// lwe11b (c2opt/alg stream, 2026-10-21) = the AVX2 build of lwe11 rc11 (lwe11b5): identical algorithm and tables; the translation of",
        "// lwe11b (c2opt/alg stream, 2026-10-22) = the AVX2 build of lwe11 rc13 (lwe11b6): identical algorithm and tables; the translation of")
    rep("// compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n",
        "// compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n" + NOTE.replace("//    rc13:", "// rc13:").replace("\n//    ", "\n// "))

# 3. bit cache
rep("static signed char *LBlev = NULL; static long long lbprune[41], lbchecked = 0;\n",
    "static signed char *LBlev = NULL; static long long lbprune[41], lbchecked = 0;\n"
    "static uint8_t *LBval = NULL; static unsigned long long *LBvst = NULL;   // rc13: bit (g, j) cached while LBvst = nid[L_j + 1]\n"
    "static int *LBglv = NULL; static unsigned long long *LBgst = NULL;      // rc13: g compared greater on bits of levels <= LBglv[g]: valid while LBgst = nid[LBglv + 1]\n")
rep("    LBc = malloc((size_t)LBnG * LBm0); LBlev = malloc((size_t)LBnG * LBm0);\n",
    "    LBc = malloc((size_t)LBnG * LBm0); LBlev = malloc((size_t)LBnG * LBm0);\n"
    "    LBval = calloc((size_t)LBnG * LBm0 + 1, 1); LBvst = calloc((size_t)LBnG * LBm0 + 1, sizeof(unsigned long long));\n"
    "    LBglv = calloc((size_t)LBnG + 1, sizeof(int)); LBgst = calloc((size_t)LBnG + 1, sizeof(unsigned long long));\n")
rep("""static int lb_reject_fast(int t) {         // same decision as lb_reject_full, over the trigger list of level t
    const int s0 = syn_ep(LHc0);
    for (int q = LBts[t]; q < LBts[t + 1]; q++) {
        const int g = LBtg[q]; const size_t o0 = (size_t)g * LBm0;
        for (int j = LBm0 - 1; j >= 0; j--) {
            const size_t o = o0 + j;
            if (LBlev[o] > t - 1) break;
            const int b = par128(LBF[o] & asg) ^ LBc[o], sb = (s0 >> j) & 1;""",
    """static int lb_reject_fast(int t) {         // same decision as lb_reject_full, over the trigger list of level t
    const int s0 = syn_ep(LHc0), lv0 = C[LHc0].lv;
    for (int q = LBts[t]; q < LBts[t + 1]; q++) {
        const int g = LBtg[q]; const size_t o0 = (size_t)g * LBm0;
        if (LBglv[g] + 1 <= t && LBgst[g] == nid[LBglv[g] + 1]) continue;   // rc13: g already compared greater at this ancestor
                                                   // (nid[e] identifies the current path only for e <= t)
        int dl = lv0;                              // the comparison so far depends on s0 and on the bits read
        for (int j = LBm0 - 1; j >= 0; j--) {
            const size_t o = o0 + j;
            const int lv = LBlev[o];
            if (lv > t - 1) break;
            int b;                                 // rc13: the bit depends on levels <= lv only, cached per ancestor of level lv + 1
            if (LBvst[o] == nid[lv + 1]) b = LBval[o];
            else { b = par128(LBF[o] & asg) ^ LBc[o]; LBval[o] = (uint8_t)b; LBvst[o] = nid[lv + 1]; }
            if (lv > dl) dl = lv;
            const int sb = (s0 >> j) & 1;""")

rep("""            if (lv > dl) dl = lv;
            const int sb = (s0 >> j) & 1;
            if (b < sb) return 1;
            if (b > sb) break;
        }
    }
    return 0;
}""", """            if (lv > dl) dl = lv;
            const int sb = (s0 >> j) & 1;
            if (b < sb) return 1;
            if (b > sb) { LBglv[g] = dl; LBgst[g] = nid[dl + 1]; break; }   // same outcome everywhere below that ancestor
        }
    }
    return 0;
}""")

# 2. static per-level buffers for the bulk masks
rep("static void kids_loop_b(LV *L, int t, const uint16_t *S, const u64 *w) {   // kids loop with bulk LTSH for the children\n"
    "    u64 P[128 * 8] __attribute__((aligned(64))), T[128 * 8] __attribute__((aligned(64)));\n",
    "static u64 *PTB[42];                       // rc13: per level, P and T (nwords each, 64-byte aligned) for kids_loop_b\n"
    "static void kids_loop_b(LV *L, int t, const uint16_t *S, const u64 *w) {   // kids loop with bulk LTSH for the children\n"
    "    u64 *P = PTB[t], *T = PTB[t] + ((L->nwords + 7) / 8) * 8;\n")
if isa == 'avx512':
    rep("    const int nz = L->nz; __m512i acc[128], tac[128];\n",
        "    const int nz = L->nz; __m512i *acc = BACC[t], *tac = BACC[t] + nz;   // rc13: per-level accumulators, not 16 KB of stack\n")
    rep("static int bulk_mask(LV *L, int t, const uint16_t *S, const u64 *w, u64 *P, u64 *T) {",
        "static __m512i *BACC[42];                  // rc13: per level, 2 x nz accumulators for bulk_mask\n"
        "static int bulk_mask(LV *L, int t, const uint16_t *S, const u64 *w, u64 *P, u64 *T) {")

# 1. the wide multi-ZMM path of search_fast into its own function (keeps search_fast's frame small)
if isa == 'avx512':   # the AVX2 source already keeps its wide path (filter_generic) in its own function
    a0 = "    // multi-ZMM bitmaps (kt >= 10), list mode below L->thr survivors\n"
    a1 = "    kids_loop_b(L, t, S, w);\n}\nstatic void search(int t) {"
    if s.count(a0) != 1: sys.exit("wide-path anchor not unique")
    i0 = s.index(a0); i1 = s.index(a1, i0)
    body = s[i0:i1]
    s = (s[:i0] + "    search_fast_wide(L, t, S);\n}\n"
         "static void search_fast_wide(LV *L, int t, const uint16_t *S) {   // rc13: the wide paths, outside search_fast's frame\n"
         "    const int nr0 = L->nr0, ntr = L->ntr, nc = L->nc;\n"
         + body + s[i1:])
    rep("static void search_fast(int t) {\n",
        "static void search_fast_wide(LV *L, int t, const uint16_t *S) __attribute__((noinline));\n"
        "static void search_fast(int t) {\n")

# allocate the buffers once the levels are known
rep("    for (int t = 0; t < NLEV; t++) alive[t] = malloc(sizeof(u64) * (((1L << kmax) + 63) / 64 + 1));\n",
    "    for (int t = 0; t < NLEV; t++) alive[t] = malloc(sizeof(u64) * (((1L << kmax) + 63) / 64 + 1));\n"
    "    for (int t = 0; t < NLEV; t++) {        // rc13: bulk mask buffers per level\n"
    "        const int k = vstart[t + 1] - vstart[t]; const long nw = k >= 6 ? 1L << (k - 6) : 1, nw8 = (nw + 7) / 8 * 8;\n"
    "        PTB[t] = aligned_alloc(64, sizeof(u64) * (size_t)(2 * nw8 + 16)); if (!PTB[t]) die(\"alloc\"); memset(PTB[t], 0, sizeof(u64) * (size_t)(2 * nw8 + 16));\n"
    + ("        const long nz = nw8 / 8 > 0 ? nw8 / 8 : 1; BACC[t] = aligned_alloc(64, sizeof(__m512i) * (size_t)(2 * nz + 2)); if (!BACC[t]) die(\"alloc\");\n" if isa == 'avx512' else "")
    + "    }\n")

# 4. kt = 10: stop translating a half of the bitmap once it is all dead
if isa == 'avx512':
    rep("""        int i = nr0; const int iend = nr0 + ntr;
        for (; i + 1 < iend; i += 2) {
            __m512i P0, P1, Q0, Q1; TR2(i, P0, P1); TR2(i + 1, Q0, Q1);
            a0 = _mm512_andnot_si512(_mm512_or_si512(P0, Q0), a0); a1 = _mm512_andnot_si512(_mm512_or_si512(P1, Q1), a1);
            if (!_mm512_test_epi64_mask(_mm512_or_si512(a0, a1), _mm512_or_si512(a0, a1))) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        for (; i < iend; i++) {
            __m512i P0, P1; TR2(i, P0, P1);
            a0 = _mm512_andnot_si512(P0, a0); a1 = _mm512_andnot_si512(P1, a1);
            if (!_mm512_test_epi64_mask(_mm512_or_si512(a0, a1), _mm512_or_si512(a0, a1))) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
""", """        int i = nr0; const int iend = nr0 + ntr; int hz = -1;   // rc13: hz = byte offset of the only live half
        for (; i + 1 < iend; i += 2) {
            __m512i P0, P1, Q0, Q1; TR2(i, P0, P1); TR2(i + 1, Q0, Q1);
            a0 = _mm512_andnot_si512(_mm512_or_si512(P0, Q0), a0); a1 = _mm512_andnot_si512(_mm512_or_si512(P1, Q1), a1);
            const __mmask8 m0 = _mm512_test_epi64_mask(a0, a0), m1 = _mm512_test_epi64_mask(a1, a1);
            if (!(m0 && m1)) {
                if (!m0 && !m1) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
                hz = m0 ? 0 : 64; i += 2; break;
            }
        }
        if (hz < 0) {
            for (; i < iend; i++) {
                __m512i P0, P1; TR2(i, P0, P1);
                a0 = _mm512_andnot_si512(P0, a0); a1 = _mm512_andnot_si512(P1, a1);
                if (!_mm512_test_epi64_mask(_mm512_or_si512(a0, a1), _mm512_or_si512(a0, a1))) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
            }
        } else {                                   // rc13: one half is all dead; translate only the live half
#define TRH(i, B) do { uint32_t s_ = S[i]; uint32_t e_ = CVL[(size_t)(i) * 64 + (s_ & 63)] ^ CVH[(size_t)(i) * hs + (s_ >> 6)]; \\
            B = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(OPT_IDX(e_), _mm512_loadu_si512((const void *)(AR + (e_ >> 10) + (((e_ >> 3) & 64) ^ (uint32_t)hz)))), \\
                                              _mm512_set1_epi64((long long)AFF[e_ & 7]), 0); } while (0)
            __m512i a = hz ? a1 : a0;
            for (; i + 1 < iend; i += 2) {
                __m512i P, Q; TRH(i, P); TRH(i + 1, Q);
                a = _mm512_andnot_si512(_mm512_or_si512(P, Q), a);
                if (!_mm512_test_epi64_mask(a, a)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
            }
            for (; i < iend; i++) {
                __m512i P; TRH(i, P);
                a = _mm512_andnot_si512(P, a);
                if (!_mm512_test_epi64_mask(a, a)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
            }
            if (hz) a1 = a; else a0 = a;
        }
""")

# 5. child fusion at levels without node tests
rep("static void search(int t);\n",
    "static void search(int t);\n"
    "static void search_fast(int t);\n"
    "static unsigned char fuse_lv[42];         // rc13: level whose nodes have no test: the parent calls search_fast directly\n")
rep("""            newdone[t + 1] = (unsigned char)(T && !((T[i] >> j) & 1));
            search(t + 1);
""", """            newdone[t + 1] = (unsigned char)(T && !((T[i] >> j) & 1));
            if (fz) { nid[t + 1] = ++NIDC; SETLEV(t + 1); nodes[t + 1]++; if (!stopflag) search_fast(t + 1); }   // rc13: = search(t + 1) there
            else search(t + 1);
""")
rep("""    const int fs = fsplit_ok && t + 1 == SPL;
""", """    const int fs = fsplit_ok && t + 1 == SPL, fz = fuse_lv[t + 1];
""")
rep("""    fsplit_ok = SPL > 0 && SPL < NLEV && !SYM && !LR && !(LH && lhact[SPL]) && !(LB && lbact[SPL]) && !getenv("LWE11NOFASTSPLIT");
""", """    fsplit_ok = SPL > 0 && SPL < NLEV && !SYM && !LR && !(LH && lhact[SPL]) && !(LB && lbact[SPL]) && !getenv("LWE11NOFASTSPLIT");
    for (int l = 1; l < NLEV; l++)          // rc13: child fusion where search() would run no test before search_fast
        fuse_lv[l] = (unsigned char)(!CHECK && !SYM && !LR && !(LH && lhact[l]) && !(LB && lbact[l]) && l != SPL && LVL[l].on && !getenv("LWE11NOFUSE"));
""")

open(dst, 'w').write(s)
print("patched", src, "->", dst)
