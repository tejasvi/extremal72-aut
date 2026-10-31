"""patch_rc12.py SRC DST : rc12 = rc11 + exact hoisting of parent-invariant lanes (order3-class's finding, generalised).
At a level t with one-ZMM bitmaps (kt <= 9), the translate / direct-table lanes whose syndrome depends on the parent's
row x_{t-1} only through a d-dimensional projection beta = P x_{t-1} (d <= HDMAX, default 1) form a hoist group.  When a
node of level t-1 has >= HTHR (default 4) alive children, it ORs the group's bad-children bitmaps once per beta
(2^d bitmaps, from its own s0 vector of level t's lanes); each child of level t then starts from the complement of the
bitmap for its beta and runs only the other lanes.  The alive sets, and so the search tree and all counts, are
unchanged; LWE11CHECK verifies each child's hoisted bitmap and alive set against a direct computation.
AVX-512 only (frozen_rc11/lwe11.c as base).  Exact anchors, each must occur once."""
import sys

src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()


def rep(old, new, cnt=1):
    global s
    n = s.count(old)
    if n != cnt:
        sys.exit(f"anchor found {n} times (want {cnt}): {old[:90]!r}")
    s = s.replace(old, new)


rep("// lwe11 (c2opt/alg stream, 2026-10-21, release rc11) = lwe10 with a new level filter; same search tree, same pruning decisions,",
    "// lwe11 (c2opt/alg stream, 2026-10-21, release rc12) = lwe10 with a new level filter; same search tree, same pruning decisions,")
rep("//    compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n",
    "//    compares with the prototype's full loop.  Without LTSBFILE nothing changes.\n"
    "//    rc12: lanes whose syndrome depends on the parent's row only through a d-dim projection (d <= 1 by default) are\n"
    "//    hoisted: the parent ORs their bad-children bitmaps once per projection value, each child starts from that\n"
    "//    (kt <= 9 levels; same alive sets; LWE12NOHOIST=1 turns it off).\n")

# LV fields
rep("    int ndir, de; uint8_t *DT; uint32_t *DOFF; int arena;",
    "    int nhg, hd, nh1, nh2; uint8_t *PX; uint16_t *HOFF;   // rc12 hoist group: lanes, projection dim, hoisted arena / direct lanes (last of each sub-range), beta = PX[x_{t-1}], s0 offsets HOFF[4i + beta]\n"
    "    int ndir, de; uint8_t *DT; uint32_t *DOFF; int arena;")

# globals
rep("static long long fastnodes = 0, checknodes = 0;\n",
    "static long long fastnodes = 0, checknodes = 0;\n"
    "static __m512i HB[42][4];                // rc12: hoisted bad-children bitmaps of level t per beta, valid while hst[t] == nid[t-1]\n"
    "static unsigned long long hst[42]; static int HOIST = 1, HTHR = 4, HDMAX = 1; static long long hoistn[42], hoistu[42];\n")

# lane order with hoist groups (build_fast)
rep("        for (int k = 0; k < 4; k++) for (int i = 0; i < nc; i++) if (cls[i] == k) L->cid[pos++] = ORD[lstart[t] + i];\n",
    "        // rc12: hoist group among translate / direct lanes (class 1, 2), greedy by parent-row rank, joint rank <= HDMAX\n"
    "        unsigned char *hm = calloc(nc + 1, 1); int hd = 0; uint64_t hb[16]; int ng = 0;\n"
    "        if (HOIST && t >= 1 && L->nz == 1 && vstart[t] - vstart[t - 1] <= 14) {\n"
    "            const int pk = vstart[t] - vstart[t - 1], pl = vstart[t - 1]; const uint64_t pmk = (1ULL << pk) - 1;\n"
    "            uint64_t *rb = calloc((size_t)16 * (nc + 1), sizeof(uint64_t)); int *rr = calloc(nc + 1, sizeof(int));\n"
    "            for (int i = 0; i < nc; i++) {   // row space of each lane's dependence on the parent row (basis sorted, reduced)\n"
    "                if (cls[i] != 1 && cls[i] != 2) { rr[i] = 99; continue; }\n"
    "                const Con *X = &C[ORD[lstart[t] + i]]; uint64_t *b = rb + 16 * i; int r = 0;\n"
    "                for (int q = 0; q < X->m; q++) { uint64_t v = (uint64_t)(X->fm[q] >> pl) & pmk; for (int z = 0; z < r; z++) if ((v ^ b[z]) < v) v ^= b[z]; if (v) { b[r++] = v; for (int a = r - 1; a > 0 && b[a] > b[a - 1]; a--) { uint64_t x = b[a]; b[a] = b[a - 1]; b[a - 1] = x; } } }\n"
    "                rr[i] = r;\n"
    "            }\n"
    "            for (int i = 0; i < nc; i++) if (rr[i] == 0) { hm[i] = 1; ng++; }   // independent of the parent row: one bitmap\n"
    "            for (int dd = 0; dd < HDMAX; dd++) {   // add the most frequent direction among the remaining rank-1 lanes\n"
    "                uint64_t bestv = 0; int bestc = 0;\n"
    "                for (int i = 0; i < nc; i++) if (!hm[i] && rr[i] == 1) { uint64_t v = rb[16 * i]; for (int z = 0; z < hd; z++) if ((v ^ hb[z]) < v) v ^= hb[z]; if (!v) continue;\n"
    "                    int c = 0; for (int k = 0; k < nc; k++) if (!hm[k] && rr[k] == 1) { uint64_t u = rb[16 * k]; for (int z = 0; z < hd; z++) if ((u ^ hb[z]) < u) u ^= hb[z]; if (u == v) c++; }\n"
    "                    if (c > bestc) { bestc = c; bestv = v; } }\n"
    "                if (!bestc) break;\n"
    "                hb[hd++] = bestv; for (int a = hd - 1; a > 0 && hb[a] > hb[a - 1]; a--) { uint64_t x = hb[a]; hb[a] = hb[a - 1]; hb[a - 1] = x; }\n"
    "                for (int a = 0; a < hd; a++) for (int z = a + 1; z < hd; z++) if ((hb[a] ^ hb[z]) < hb[a]) hb[a] ^= hb[z];\n"
    "            }\n"
    "            for (int i = 0; i < nc; i++) if (!hm[i] && rr[i] >= 1 && rr[i] <= hd) {   // every lane whose row space lies in span(hb)\n"
    "                int in = 1; for (int q = 0; q < rr[i] && in; q++) { uint64_t v = rb[16 * i + q]; for (int z = 0; z < hd; z++) if ((v ^ hb[z]) < v) v ^= hb[z]; if (v) in = 0; }\n"
    "                if (in) { hm[i] = 1; ng++; }\n"
    "            }\n"
    "            free(rb); free(rr);\n"
    "            if (ng < 2) { memset(hm, 0, nc + 1); ng = 0; hd = 0; }\n"
    "        }\n"
    "        L->nhg = ng; L->hd = hd; L->nh1 = 0; L->nh2 = 0;\n"
    "        for (int k = 0; k < 4; k++) for (int hh = 0; hh < 2; hh++) for (int i = 0; i < nc; i++) if (cls[i] == k && hm[i] == hh) {\n"
    "            L->cid[pos++] = ORD[lstart[t] + i]; if (hh && k == 1) L->nh1++; if (hh && k == 2) L->nh2++; }\n"
    "        if (ng) {   // projection beta = PX[x_{t-1}] (bit z = parity(hb[z] & x)) and s0 offsets per hoisted lane\n"
    "            const int pk = vstart[t] - vstart[t - 1], pl = t - 1; L->PX = malloc((size_t)1 << pk);\n"
    "            for (long x = 0; x < (1L << pk); x++) { int b = 0; for (int z = 0; z < hd; z++) b |= (__builtin_popcountll(hb[z] & (uint64_t)x) & 1) << z; L->PX[x] = (uint8_t)b; }\n"
    "            long xr[4] = {-1, -1, -1, -1}; for (long x = 0; x < (1L << pk); x++) if (xr[L->PX[x]] < 0) xr[L->PX[x]] = x;\n"
    "            L->HOFF = calloc((size_t)4 * (nc + 1), sizeof(uint16_t));\n"
    "            for (int i = 0; i < nc; i++) {\n"
    "                const Con *X = &C[L->cid[i]];\n"
    "                for (int b = 0; b < (1 << hd); b++) { uint32_t o = 0; for (int j = 0; j < pk; j++) if ((xr[b] >> j) & 1) o ^= colL(X, pl, j); L->HOFF[(size_t)4 * i + b] = (uint16_t)o; }\n"
    "            }\n"
    "        }\n"
    "        free(hm);\n")

# finish hoist setup when the level is complete (needs nr0/ntr/ndir, vec, arena); verify the projection on hoisted lanes
rep("        L->on = 1;\n",
    "        if (L->nhg) {   // rc12: hoisting needs one-ZMM bitmaps, s0 vectors and the arena layout\n"
    "            if (!(L->nz == 1 && L->vec && L->arena)) L->nhg = 0;\n"
    "            else {\n"
    "                const int pk = vstart[t] - vstart[t - 1];\n"
    "                const int a1 = L->nr0 + L->ntr - L->ndir - L->nh1, a2 = L->nr0 + L->ntr - L->ndir, d1 = L->nr0 + L->ntr - L->nh2, d2 = L->nr0 + L->ntr;\n"
    "                for (int i = 0; i < L->nc; i++) {\n"
    "                    const int hoisted = (i >= a1 && i < a2) || (i >= d1 && i < d2); if (!hoisted) continue;\n"
    "                    const Con *X = &C[L->cid[i]];\n"
    "                    for (long x = 0; x < (1L << pk); x++) { uint32_t o = 0; for (int j = 0; j < pk; j++) if ((x >> j) & 1) o ^= colL(X, t - 1, j);\n"
    "                        if (o != L->HOFF[(size_t)4 * i + L->PX[x]]) die(\"rc12: hoist projection inconsistent\"); }\n"
    "                }\n"
    "            }\n"
    "        }\n"
    "        L->on = 1;\n")

# hoist computation and check (before check_node)
rep("static void check_node(LV *L, int t, const uint16_t *S, const u64 *alive, int dead) {   // LWE11CHECK\n",
    "static inline __m512i hoist_lane(const LV *L, int i, uint32_t s) {   // bad-children bitmap of hoisted lane i for s0 = s\n"
    "    if (i >= L->nr0 + L->ntr - L->ndir) return _mm512_loadu_si512((const void *)(L->DT + L->DOFF[i] + (size_t)s * L->de));\n"
    "    const uint32_t e = L->CVL[(size_t)i * 64 + (s & 63)] ^ L->CVH[(size_t)i * L->hs + (s >> 6)];\n"
    "    __m512i B = _mm512_loadu_si512((const void *)(L->AR + (e >> 9)));\n"
    "    B = _mm512_permutexvar_epi8(OPT_IDX(e), B);\n"
    "    return _mm512_gf2p8affine_epi64_epi8(B, _mm512_set1_epi64((long long)AFF[e & 7]), 0);\n"
    "}\n"
    "static inline const uint16_t *s0vec(LV *L, int t);\n"
    "static void hoist_compute(int t) {      // rc12: at a node of level t-1, the hoist group's bitmaps of its children\n"
    "    LV *L = &LVL[t]; const uint16_t *Sb = s0vec(L, t - 1);   // level-t lanes, contributions of levels < t-1\n"
    "    const int a1 = L->nr0 + L->ntr - L->ndir - L->nh1, a2 = L->nr0 + L->ntr - L->ndir, d1 = L->nr0 + L->ntr - L->nh2, d2 = L->nr0 + L->ntr;\n"
    "    for (int b = 0; b < (1 << L->hd); b++) {\n"
    "        __m512i acc = _mm512_setzero_si512();\n"
    "        for (int i = a1; i < a2; i++) acc = _mm512_or_si512(acc, hoist_lane(L, i, (uint32_t)(Sb[i] ^ L->HOFF[(size_t)4 * i + b])));\n"
    "        for (int i = d1; i < d2; i++) acc = _mm512_or_si512(acc, hoist_lane(L, i, (uint32_t)(Sb[i] ^ L->HOFF[(size_t)4 * i + b])));\n"
    "        HB[t][b] = acc;\n"
    "    }\n"
    "    hst[t] = nid[t - 1]; hoistn[t]++;\n"
    "}\n"
    "static void hoist_check(const LV *L, int t, const uint16_t *S, __m512i h) {   // LWE11CHECK: hoisted bitmap from the child's own s0\n"
    "    const int a1 = L->nr0 + L->ntr - L->ndir - L->nh1, a2 = L->nr0 + L->ntr - L->ndir, d1 = L->nr0 + L->ntr - L->nh2, d2 = L->nr0 + L->ntr;\n"
    "    __m512i acc = _mm512_setzero_si512();\n"
    "    for (int i = a1; i < a2; i++) acc = _mm512_or_si512(acc, hoist_lane(L, i, S[i]));\n"
    "    for (int i = d1; i < d2; i++) acc = _mm512_or_si512(acc, hoist_lane(L, i, S[i]));\n"
    "    const __m512i m = _mm512_load_si512((const void *)L->allm);\n"
    "    if (_mm512_test_epi64_mask(_mm512_and_si512(_mm512_xor_si512(acc, h), m), _mm512_and_si512(_mm512_xor_si512(acc, h), m))) { fprintf(stderr, \"CHECK hoisted bitmap mismatch at level %d\\n\", t); exit(3); }\n"
    "}\n"
    "static void check_node(LV *L, int t, const uint16_t *S, const u64 *alive, int dead) {   // LWE11CHECK\n")

# kids_loop_p: compute the hoist for the children's level
rep("static void kids_loop_p(int t, const u64 *w, int nwords, const u64 *P, const u64 *T) {\n"
    "    u128 clearmask = ~(((((u128)1) << (vstart[t + 1] - vstart[t])) - 1) << vstart[t]);\n",
    "static void kids_loop_p(int t, const u64 *w, int nwords, const u64 *P, const u64 *T) {\n"
    "    u128 clearmask = ~(((((u128)1) << (vstart[t + 1] - vstart[t])) - 1) << vstart[t]);\n"
    "    if (t + 1 < NLEV && LVL[t + 1].nhg && !probe_mode) {   // rc12: hoist the children's parent-invariant lanes\n"
    "        long cnt = 0; for (int i = 0; i < nwords; i++) cnt += __builtin_popcountll(w[i]);\n"
    "        if (cnt >= HTHR) hoist_compute(t + 1);\n"
    "    }\n")

# narrow paths (kt <= 8): start from the hoisted bitmap, skip the hoisted lanes
rep("        const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const int iend = nr0 + ntr - L->ndir, dend = nr0 + ntr;\n"
    "        u64 w[8] __attribute__((aligned(64))) = {0};\n",
    "        const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const int iend = nr0 + ntr - L->ndir, dend = nr0 + ntr;\n"
    "        u64 w[8] __attribute__((aligned(64))) = {0};\n"
    "        const int hv = L->nhg && hst[t] == nid[t - 1];   // rc12: hoisted bitmap valid for this child\n"
    "        const __m512i hz = hv ? HB[t][L->PX[xv[t - 1]]] : _mm512_setzero_si512();\n"
    "        if (hv) { hoistu[t]++; if (CHECK) hoist_check(L, t, S, hz); }\n"
    "        const int ie = iend - (hv ? L->nh1 : 0), de2 = dend - (hv ? L->nh2 : 0);\n")
rep("            __m256i al = _mm256_load_si256((const __m256i *)L->allm); const __m256i io = _mm512_castsi512_si256(IOTA);\n",
    "            __m256i al = _mm256_andnot_si256(_mm512_castsi512_si256(hz), _mm256_load_si256((const __m256i *)L->allm)); const __m256i io = _mm512_castsi512_si256(IOTA);\n")
rep("            int i = nr0;\n"
    "            for (; i + 1 < iend; i += 2) { __m256i B0, B1; TRY(i, B0); TRY(i + 1, B1); al = _mm256_andnot_si256(_mm256_or_si256(B0, B1), al); if (_mm256_testz_si256(al, al)) goto dead; }\n"
    "            for (; i < iend; i++) { __m256i B0; TRY(i, B0); al = _mm256_andnot_si256(B0, al); if (_mm256_testz_si256(al, al)) goto dead; }\n"
    "            for (; i + 1 < dend; i += 2) {",
    "            if (_mm256_testz_si256(al, al)) goto dead;\n"
    "            int i = nr0;\n"
    "            for (; i + 1 < ie; i += 2) { __m256i B0, B1; TRY(i, B0); TRY(i + 1, B1); al = _mm256_andnot_si256(_mm256_or_si256(B0, B1), al); if (_mm256_testz_si256(al, al)) goto dead; }\n"
    "            for (; i < ie; i++) { __m256i B0; TRY(i, B0); al = _mm256_andnot_si256(B0, al); if (_mm256_testz_si256(al, al)) goto dead; }\n"
    "            i = iend;\n"
    "            for (; i + 1 < de2; i += 2) {")
rep("            for (; i < dend; i++) { al = _mm256_andnot_si256(_mm256_load_si256((const __m256i *)(DT + DOFF[i] + (size_t)S[i] * 32)), al); if (_mm256_testz_si256(al, al)) goto dead; }\n",
    "            for (; i < de2; i++) { al = _mm256_andnot_si256(_mm256_load_si256((const __m256i *)(DT + DOFF[i] + (size_t)S[i] * 32)), al); if (_mm256_testz_si256(al, al)) goto dead; }\n")
rep("            __m128i al = _mm_load_si128((const __m128i *)L->allm); const __m128i io = _mm512_castsi512_si128(IOTA);\n",
    "            __m128i al = _mm_andnot_si128(_mm512_castsi512_si128(hz), _mm_load_si128((const __m128i *)L->allm)); const __m128i io = _mm512_castsi512_si128(IOTA);\n")
rep("            int i = nr0;\n"
    "            for (; i + 1 < iend; i += 2) { __m128i B0, B1; TRX(i, B0); TRX(i + 1, B1); al = _mm_andnot_si128(_mm_or_si128(B0, B1), al); if (_mm_testz_si128(al, al)) goto dead; }\n"
    "            for (; i < iend; i++) { __m128i B0; TRX(i, B0); al = _mm_andnot_si128(B0, al); if (_mm_testz_si128(al, al)) goto dead; }\n"
    "            for (; i + 1 < dend; i += 2) {",
    "            if (_mm_testz_si128(al, al)) goto dead;\n"
    "            int i = nr0;\n"
    "            for (; i + 1 < ie; i += 2) { __m128i B0, B1; TRX(i, B0); TRX(i + 1, B1); al = _mm_andnot_si128(_mm_or_si128(B0, B1), al); if (_mm_testz_si128(al, al)) goto dead; }\n"
    "            for (; i < ie; i++) { __m128i B0; TRX(i, B0); al = _mm_andnot_si128(B0, al); if (_mm_testz_si128(al, al)) goto dead; }\n"
    "            i = iend;\n"
    "            for (; i + 1 < de2; i += 2) {")
rep("            for (; i < dend; i++) { al = _mm_andnot_si128(_mm_load_si128((const __m128i *)(DT + DOFF[i] + (size_t)S[i] * 16)), al); if (_mm_testz_si128(al, al)) goto dead; }\n",
    "            for (; i < de2; i++) { al = _mm_andnot_si128(_mm_load_si128((const __m128i *)(DT + DOFF[i] + (size_t)S[i] * 16)), al); if (_mm_testz_si128(al, al)) goto dead; }\n")
rep("            u64 al = L->allm[0]; const __m128i io = _mm512_castsi512_si128(IOTA);\n",
    "            u64 al = L->allm[0] & ~(u64)_mm_cvtsi128_si64(_mm512_castsi512_si128(hz)); const __m128i io = _mm512_castsi512_si128(IOTA);\n")
rep("            int i = nr0;\n"
    "            for (; i + 1 < iend; i += 2) { u64 B0, B1; TRQ(i, B0); TRQ(i + 1, B1); al &= ~(B0 | B1); if (!al) goto dead; }\n"
    "            for (; i < iend; i++) { u64 B0; TRQ(i, B0); al &= ~B0; if (!al) goto dead; }\n"
    "            for (; i + 1 < dend; i += 2) {",
    "            if (!al) goto dead;\n"
    "            int i = nr0;\n"
    "            for (; i + 1 < ie; i += 2) { u64 B0, B1; TRQ(i, B0); TRQ(i + 1, B1); al &= ~(B0 | B1); if (!al) goto dead; }\n"
    "            for (; i < ie; i++) { u64 B0; TRQ(i, B0); al &= ~B0; if (!al) goto dead; }\n"
    "            i = iend;\n"
    "            for (; i + 1 < de2; i += 2) {")
rep("            for (; i < dend; i++) { u64 b0; memcpy(&b0, DT + DOFF[i] + (size_t)S[i] * 8, 8); al &= ~b0; if (!al) goto dead; }\n",
    "            for (; i < de2; i++) { u64 b0; memcpy(&b0, DT + DOFF[i] + (size_t)S[i] * 8, 8); al &= ~b0; if (!al) goto dead; }\n")

# kt = 9 one-ZMM arena path
rep("        if (L->vec && L->arena) {\n"
    "            const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;\n"
    "#define TR1(i, B)",
    "        if (L->vec && L->arena) {\n"
    "            const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;\n"
    "            const int hv = L->nhg && hst[t] == nid[t - 1];   // rc12: hoisted bitmap valid for this child\n"
    "            if (hv) { const __m512i hz = HB[t][L->PX[xv[t - 1]]]; hoistu[t]++; if (CHECK) hoist_check(L, t, S, hz); al = _mm512_andnot_si512(hz, al);\n"
    "                if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; } }\n"
    "#define TR1(i, B)")
rep("            int i = nr0; const int iend = nr0 + ntr - L->ndir;\n"
    "#if OPT_UNROLL2\n"
    "            for (; i + 1 < iend; i += 2) {\n"
    "                __m512i B0, B1; TR1(i, B0); TR1(i + 1, B1);\n",
    "            int i = nr0; const int iend0 = nr0 + ntr - L->ndir, iend = iend0 - (hv ? L->nh1 : 0);\n"
    "#if OPT_UNROLL2\n"
    "            for (; i + 1 < iend; i += 2) {\n"
    "                __m512i B0, B1; TR1(i, B0); TR1(i + 1, B1);\n")
rep("            if (L->ndir) {\n"
    "                const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const size_t de = (size_t)L->de; const int dend = nr0 + ntr;\n",
    "            i = iend0;\n"
    "            if (L->ndir) {\n"
    "                const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const size_t de = (size_t)L->de; const int dend = nr0 + ntr - (hv ? L->nh2 : 0);\n")

# environment and statistics
rep("    CHECK = getenv(\"LWE11CHECK\") != NULL;\n",
    "    CHECK = getenv(\"LWE11CHECK\") != NULL;\n")
rep("    build_fast();\n",
    "    if (getenv(\"LWE12NOHOIST\")) HOIST = 0;\n"
    "    if (getenv(\"LWE12HTHR\")) HTHR = atoi(getenv(\"LWE12HTHR\"));\n"
    "    if (getenv(\"LWE12HDMAX\")) { HDMAX = atoi(getenv(\"LWE12HDMAX\")); if (HDMAX < 0) HDMAX = 0; if (HDMAX > 2) HDMAX = 2; }\n"
    "    build_fast();\n"
    "    if (getenv(\"LWE11VERB\")) for (int t = 0; t < NLEV; t++) if (LVL[t].nhg) fprintf(stderr, \"rc12: level %d hoist group %d lanes (arena %d, direct %d), d %d\\n\", t, LVL[t].nhg, LVL[t].nh1, LVL[t].nh2, LVL[t].hd);\n")
rep('    if (CHECK) fprintf(stderr, "LWE11CHECK passed: %lld fast nodes checked\\n", checknodes);\n',
    '    if (getenv("LWE11VERB")) for (int t = 0; t < NLEV; t++) if (hoistn[t]) fprintf(stderr, "rc12: level %d hoists %lld, children using them %lld\\n", t, hoistn[t], hoistu[t]);\n'
    '    if (CHECK) fprintf(stderr, "LWE11CHECK passed: %lld fast nodes checked\\n", checknodes);\n')

open(dst, 'w').write(s)
print("patched", src, "->", dst)
