// ---- lwe11b: AVX2 level filter (<CPU>/3, Haswell+).  Same tables and layouts as lwe11; only the translation differs:
// bytes move by XOR with D = v0 >> 3 (128-bit lane swap for bit 4 of D, VPSHUFB for bits 0-3, 32-byte blocks for
// higher bits), bits inside a byte move by XOR with v0 & 7 (two nibble lookups with VPSHUFB).
static __m256i SHUFY[16], LANEIDX[2], BTL[8], BTH[8], LO4;
static __m128i SHUFX[16], BTLX[8], BTHX[8], LO4X;
static void init_avx2_tables(void) {
    for (int d = 0; d < 16; d++) { uint8_t q[32]; for (int j = 0; j < 32; j++) q[j] = (uint8_t)((j & 15) ^ d); SHUFY[d] = _mm256_loadu_si256((const __m256i *)q); SHUFX[d] = _mm_loadu_si128((const __m128i *)q); }
    { int32_t a[8] = {0, 1, 2, 3, 4, 5, 6, 7}, b[8] = {4, 5, 6, 7, 0, 1, 2, 3}; LANEIDX[0] = _mm256_loadu_si256((const __m256i *)a); LANEIDX[1] = _mm256_loadu_si256((const __m256i *)b); }
    for (int b = 0; b < 8; b++) {            // output bit i of a byte = input bit (i ^ b): split the input into nibbles
        uint8_t tl[32], th[32];
        for (int n = 0; n < 16; n++) {
            uint8_t ol = 0, oh = 0;
            for (int i = 0; i < 8; i++) { int src = i ^ b; if (src < 4 && ((n >> src) & 1)) ol |= (uint8_t)(1u << i); if (src >= 4 && ((n >> (src - 4)) & 1)) oh |= (uint8_t)(1u << i); }
            tl[n] = tl[n + 16] = ol; th[n] = th[n + 16] = oh;
        }
        BTL[b] = _mm256_loadu_si256((const __m256i *)tl); BTH[b] = _mm256_loadu_si256((const __m256i *)th);
        BTLX[b] = _mm_loadu_si128((const __m128i *)tl); BTHX[b] = _mm_loadu_si128((const __m128i *)th);
    }
    LO4 = _mm256_set1_epi8(0x0F); LO4X = _mm_set1_epi8(0x0F);
}
static inline __m256i bperm256(__m256i x, unsigned b) {
    return _mm256_or_si256(_mm256_shuffle_epi8(BTL[b], _mm256_and_si256(x, LO4)), _mm256_shuffle_epi8(BTH[b], _mm256_and_si256(_mm256_srli_epi16(x, 4), LO4)));
}
static inline __m128i bperm128(__m128i x, unsigned b) {
    return _mm_or_si128(_mm_shuffle_epi8(BTLX[b], _mm_and_si128(x, LO4X)), _mm_shuffle_epi8(BTHX[b], _mm_and_si128(_mm_srli_epi16(x, 4), LO4X)));
}
static inline __m256i trb(const uint8_t *p, unsigned v0, int z) {     // block z (32 bytes) of the bitmap at p, translated by v0
    const unsigned D = v0 >> 3;
    __m256i x = _mm256_loadu_si256((const __m256i *)(p + ((size_t)(z ^ (int)(D >> 5)) << 5)));
    x = _mm256_shuffle_epi8(_mm256_permutevar8x32_epi32(x, LANEIDX[(D >> 4) & 1]), SHUFY[D & 15]);
    return bperm256(x, v0 & 7);
}
static inline __m128i trx16(const uint8_t *p, unsigned v0) {          // 16-byte bitmap (kt = 7)
    return bperm128(_mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)p), SHUFX[(v0 >> 3) & 15]), v0 & 7);
}
static inline u64 trx8(const uint8_t *p, unsigned v0) {               // bitmap of <= 8 bytes (kt <= 6); bits >= 2^kt are junk
    return (u64)_mm_cvtsi128_si64(bperm128(_mm_shuffle_epi8(_mm_loadl_epi64((const __m128i *)p), SHUFX[(v0 >> 3) & 7]), v0 & 7));
}
static inline int rest_lanes(LV *L, const uint16_t *S, u64 *w) {      // lanes without a translate table: child by child
    for (int i = L->nr0 + L->ntr; i < L->nc; i++) {
        const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
        for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
        if (!any) return 0;
    }
    return 1;
}
#define CVE(i) (CVL[(size_t)(i) * 64 + (S[i] & 63)] ^ CVH[(size_t)(i) * hs + (S[i] >> 6)])
static inline __attribute__((always_inline)) int filter_blk(LV *L, const uint16_t *S, u64 *w, const int nblk, const int VB) {
    // arena path, bitmaps of nblk 32-byte blocks (kt = 8, 9, 10); returns 0 when no child survives
    const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
    const uint32_t VM = (1u << VB) - 1;
    const int nr0 = L->nr0, iend = L->nr0 + L->ntr - L->ndir, dend = L->nr0 + L->ntr;
    __m256i a[4];
    for (int z = 0; z < nblk; z++) a[z] = _mm256_load_si256((const __m256i *)(L->allm + 4 * z));
    int i = nr0;
    for (; i + 1 < iend; i += 2) {
        const uint32_t e0 = CVE(i), e1 = CVE(i + 1);
        const uint8_t *p0 = AR + (e0 >> VB), *p1 = AR + (e1 >> VB); __m256i any = _mm256_setzero_si256();
        for (int z = 0; z < nblk; z++) { a[z] = _mm256_andnot_si256(_mm256_or_si256(trb(p0, e0 & VM, z), trb(p1, e1 & VM, z)), a[z]); any = _mm256_or_si256(any, a[z]); }
        if (_mm256_testz_si256(any, any)) return 0;
    }
    for (; i < iend; i++) {
        const uint32_t e0 = CVE(i); const uint8_t *p0 = AR + (e0 >> VB); __m256i any = _mm256_setzero_si256();
        for (int z = 0; z < nblk; z++) { a[z] = _mm256_andnot_si256(trb(p0, e0 & VM, z), a[z]); any = _mm256_or_si256(any, a[z]); }
        if (_mm256_testz_si256(any, any)) return 0;
    }
    if (L->ndir) {
        const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const size_t de = (size_t)L->de;
        for (; i + 1 < dend; i += 2) {
            const uint8_t *q0 = DT + DOFF[i] + S[i] * de, *q1 = DT + DOFF[i + 1] + S[i + 1] * de; __m256i any = _mm256_setzero_si256();
            for (int z = 0; z < nblk; z++) { a[z] = _mm256_andnot_si256(_mm256_or_si256(_mm256_load_si256((const __m256i *)(q0 + 32 * z)), _mm256_load_si256((const __m256i *)(q1 + 32 * z))), a[z]); any = _mm256_or_si256(any, a[z]); }
            if (_mm256_testz_si256(any, any)) return 0;
        }
        for (; i < dend; i++) {
            const uint8_t *q0 = DT + DOFF[i] + S[i] * de; __m256i any = _mm256_setzero_si256();
            for (int z = 0; z < nblk; z++) { a[z] = _mm256_andnot_si256(_mm256_load_si256((const __m256i *)(q0 + 32 * z)), a[z]); any = _mm256_or_si256(any, a[z]); }
            if (_mm256_testz_si256(any, any)) return 0;
        }
    }
    for (int z = 0; z < nblk; z++) _mm256_store_si256((__m256i *)(w + 4 * z), a[z]);
    return 1;
}
static int filter_arena(LV *L, const uint16_t *S, u64 *w) {          // L->vec and kt <= 10 (arena layout exists)
    const int kt = L->kt;
    if (kt >= 8) return kt == 8 ? filter_blk(L, S, w, 1, 9) : kt == 9 ? filter_blk(L, S, w, 2, 9) : filter_blk(L, S, w, 4, 10);
    const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
    const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF;
    const int nr0 = L->nr0, iend = L->nr0 + L->ntr - L->ndir, dend = L->nr0 + L->ntr;
    int i = nr0;
    if (kt == 7) {
        __m128i al = _mm_load_si128((const __m128i *)L->allm);
        for (; i + 1 < iend; i += 2) { const uint32_t e0 = CVE(i), e1 = CVE(i + 1); al = _mm_andnot_si128(_mm_or_si128(trx16(AR + (e0 >> 9), e0 & 511), trx16(AR + (e1 >> 9), e1 & 511)), al); if (_mm_testz_si128(al, al)) return 0; }
        for (; i < iend; i++) { const uint32_t e0 = CVE(i); al = _mm_andnot_si128(trx16(AR + (e0 >> 9), e0 & 511), al); if (_mm_testz_si128(al, al)) return 0; }
        for (; i + 1 < dend; i += 2) { al = _mm_andnot_si128(_mm_or_si128(_mm_load_si128((const __m128i *)(DT + DOFF[i] + (size_t)S[i] * 16)), _mm_load_si128((const __m128i *)(DT + DOFF[i + 1] + (size_t)S[i + 1] * 16))), al); if (_mm_testz_si128(al, al)) return 0; }
        for (; i < dend; i++) { al = _mm_andnot_si128(_mm_load_si128((const __m128i *)(DT + DOFF[i] + (size_t)S[i] * 16)), al); if (_mm_testz_si128(al, al)) return 0; }
        _mm_store_si128((__m128i *)w, al);
        return 1;
    }
    u64 al = L->allm[0];                                                 // kt <= 6: one 64-bit word
    for (; i + 1 < iend; i += 2) { const uint32_t e0 = CVE(i), e1 = CVE(i + 1); al &= ~(trx8(AR + (e0 >> 9), e0 & 511) | trx8(AR + (e1 >> 9), e1 & 511)); if (!al) return 0; }
    for (; i < iend; i++) { const uint32_t e0 = CVE(i); al &= ~trx8(AR + (e0 >> 9), e0 & 511); if (!al) return 0; }
    for (; i + 1 < dend; i += 2) { u64 b0, b1; memcpy(&b0, DT + DOFF[i] + (size_t)S[i] * 8, 8); memcpy(&b1, DT + DOFF[i + 1] + (size_t)S[i + 1] * 8, 8); al &= ~(b0 | b1); if (!al) return 0; }
    for (; i < dend; i++) { u64 b0; memcpy(&b0, DT + DOFF[i] + (size_t)S[i] * 8, 8); al &= ~b0; if (!al) return 0; }
    w[0] = al;
    return 1;
}
#undef CVE
static int filter_generic(LV *L, const uint16_t *S, u64 *w) {        // FC records, any kt <= 16; list mode below L->thr survivors
    const int kt = L->kt, nr0 = L->nr0, ntr = L->ntr, nc = L->nc, nw = L->nwords;
    const int nblk = kt >= 8 ? 1 << (kt - 8) : 0;
    memcpy(w, L->allm, sizeof(u64) * nw);
    int i = nr0;
    for (; i < nr0 + ntr; i++) {
        const FC *F = &L->fc[i];
        const uint32_t s = lane_s0(L, S, i), e = F->cvlo[s & 63] ^ F->cvhi[s >> 6];
        const uint8_t *p = F->base + (e >> 16); const unsigned v0 = e & 0xFFFF;
        if (nblk) {
            __m256i any = _mm256_setzero_si256();
            for (int z = 0; z < nblk; z++) { __m256i a = _mm256_andnot_si256(trb(p, v0, z), _mm256_load_si256((const __m256i *)(w + 4 * z))); _mm256_store_si256((__m256i *)(w + 4 * z), a); any = _mm256_or_si256(any, a); }
            if (_mm256_testz_si256(any, any)) return 0;
        } else if (kt == 7) {
            __m128i a = _mm_andnot_si128(trx16(p, v0), _mm_load_si128((const __m128i *)w)); _mm_store_si128((__m128i *)w, a); if (_mm_testz_si128(a, a)) return 0;
        } else { w[0] &= ~trx8(p, v0); if (!w[0]) return 0; }
        if (L->thr > 0 && i + 1 < nc) {
            long cnt = 0; for (int k = 0; k < nw; k++) cnt += __builtin_popcountll(w[k]);
            if (cnt <= L->thr) {                                           // list mode for the remaining lanes
                uint32_t list[64]; int nlist = 0;
                for (int k = 0; k < nw; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; list[nlist++] = (uint32_t)((k << 6) + j); } }
                for (i++; i < nr0 + ntr; i++) {
                    const FC *G = &L->fc[i]; const u64 *bb = C[L->cid[i]].badbm; const uint32_t s2 = lane_s0(L, S, i); int nl = 0;
                    for (int q = 0; q < nlist; q++) { uint32_t x = list[q]; uint32_t sv = s2 ^ G->vlo[x & 255] ^ G->vhi[x >> 8]; int bad = (int)((bb[sv >> 6] >> (sv & 63)) & 1); list[nl] = x; nl += 1 - bad; }
                    nlist = nl; if (!nlist) return 0;
                }
                for (; i < nc; i++) {
                    const Con *X = &C[L->cid[i]]; const uint32_t s2 = lane_s0(L, S, i); int nl = 0;
                    for (int q = 0; q < nlist; q++) { uint32_t x = list[q]; int bad = bad_child(X, s2, x); list[nl] = x; nl += 1 - bad; }
                    nlist = nl; if (!nlist) return 0;
                }
                memset(w, 0, sizeof(u64) * nw);
                for (int q = 0; q < nlist; q++) w[list[q] >> 6] |= 1ULL << (list[q] & 63);   // list is in increasing order
                return 2;                                                  // rest lanes already applied
            }
        }
    }
    return 1;
}
static void search_fast(int t) {
    LV *L = &LVL[t];
    fastnodes++;
    const uint16_t *S = L->vec ? s0vec(L, t) : NULL;
    const int nr0 = L->nr0;
    for (int i = 0; i < nr0; i++) { uint32_t s = lane_s0(L, S, i); if ((C[L->cid[i]].badbm[s >> 6] >> (s & 63)) & 1) { if (CHECK) check_node(L, t, S, NULL, 1); return; } }
    u64 w[1024] __attribute__((aligned(64)));
    int r;
    if (OPT_ARENA && L->vec && L->kt <= 10 && (L->ntr == 0 || L->CVL)) r = filter_arena(L, S, w);
    else r = filter_generic(L, S, w);
    if (r == 1) r = rest_lanes(L, S, w);
    if (!r) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
    if (CHECK) check_node(L, t, S, w, 0);
    kids_loop_b(L, t, S, w);
}
