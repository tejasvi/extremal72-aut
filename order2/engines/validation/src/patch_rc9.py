# Patch rc9 / lwe11b3: arena layout and specialized filter loops also for kt = 11, 12 (4 / 8 ZMMs, 8 / 16 YMM blocks);
# an oversized arena now falls back to the FC loops (flag L->arena) instead of aborting.
import sys
src, dst, isa = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(src).read()
def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old[:90], s.count(old))
    s = s.replace(old, new)
rep('    int ndir, de; uint8_t *DT; uint32_t *DOFF;', '    int ndir, de; uint8_t *DT; uint32_t *DOFF; int arena;   // arena: arena layout usable (built, or no translate lanes)')
rep('        if (L->nz <= 2 && L->ntr > 0) {        // arena layout for the one- and two-ZMM loops (VB = kt rounded up to 9 or 10)',
    '        L->arena = (L->ntr == 0);\n        if (L->nz <= 8 && L->ntr > 0) {        // arena layout for kt <= 12 (VB = v0 bits: 9 for kt <= 9, else kt)')
rep('''            const int VB = L->nz == 1 ? 9 : 10; const uint32_t VM = (1u << VB) - 1;
            if (cur >= (1L << (32 - VB))) die("arena too large");''',
'''            const int VB = L->nz == 1 ? 9 : L->nz == 2 ? 10 : L->nz == 4 ? 11 : 12; const uint32_t VM = (1u << VB) - 1;
            if (cur >= (1L << (32 - VB))) { free(sz); free(ord); free(off); goto noarena; }''')
rep('''            free(sz); free(ord); free(off);
        }''', '''            free(sz); free(ord); free(off);
            L->arena = 1;
        }
        noarena:;''')
if isa == 'avx512':
    rep('    if (L->nz == 1 && L->vec && L->kt <= 8) {   // exact-width loads and ops for bitmaps of <= 32 bytes (no line splits)',
        '    if (L->nz == 1 && L->vec && L->arena && L->kt <= 8) {   // exact-width loads and ops for bitmaps of <= 32 bytes (no line splits)')
    rep('''#if OPT_ARENA
        if (L->vec) {
            const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;''',
        '''#if OPT_ARENA
        if (L->vec && L->arena) {
            const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;''')
    rep('    if (L->nz == 2 && L->vec) {                 // kt = 10: two ZMMs, arena layout, test every 2 constraints',
        '''    if ((L->nz == 4 || L->nz == 8) && L->vec && L->arena) {   // kt = 11, 12: four / eight ZMMs, arena layout (rc9)
        u64 w[64] __attribute__((aligned(64)));
        const int r = L->nz == 4 ? filter_zn(L, S, w, 4, 11) : filter_zn(L, S, w, 8, 12);
        if (!r || !rest_lanes(L, S, w)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop_b(L, t, S, w);
        return;
    }
    if (L->nz == 2 && L->vec && L->arena) {                 // kt = 10: two ZMMs, arena layout, test every 2 constraints''')
    # filter_zn and rest_lanes helpers, placed before search_fast
    rep('static void search_fast(int t) {', '''static inline int rest_lanes(LV *L, const uint16_t *S, u64 *w) {      // lanes without a translate table: child by child
    for (int i = L->nr0 + L->ntr; i < L->nc; i++) {
        const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
        for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
        if (!any) return 0;
    }
    return 1;
}
static inline __attribute__((always_inline)) int filter_zn(LV *L, const uint16_t *S, u64 *w, const int nz, const int VB) {
    // arena path for bitmaps of nz ZMMs (kt = 11, 12); returns 0 when no child survives
    const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
    const uint32_t VM = (1u << VB) - 1;
    const int nr0 = L->nr0, iend = L->nr0 + L->ntr;
    __m512i a[8];
    for (int z = 0; z < nz; z++) a[z] = _mm512_load_si512((const void *)(L->allm + 8 * z));
#define CVEZ(i) (CVL[(size_t)(i) * 64 + (S[i] & 63)] ^ CVH[(size_t)(i) * hs + (S[i] >> 6)])
    int i = nr0;
    for (; i + 1 < iend; i += 2) {
        const uint32_t e0 = CVEZ(i), e1 = CVEZ(i + 1), v0 = e0 & VM, v1 = e1 & VM;
        const uint8_t *p0 = AR + (e0 >> VB), *p1 = AR + (e1 >> VB); const int Z0 = (int)(v0 >> 9), Z1 = (int)(v1 >> 9);
        const __m512i ix0 = OPT_IDX(v0), ix1 = OPT_IDX(v1), m0 = _mm512_set1_epi64((long long)AFF[v0 & 7]), m1 = _mm512_set1_epi64((long long)AFF[v1 & 7]);
        __m512i any = _mm512_setzero_si512();
        for (int z = 0; z < nz; z++) {
            const __m512i B0 = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix0, _mm512_loadu_si512((const void *)(p0 + ((size_t)(z ^ Z0) << 6)))), m0, 0);
            const __m512i B1 = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix1, _mm512_loadu_si512((const void *)(p1 + ((size_t)(z ^ Z1) << 6)))), m1, 0);
            a[z] = _mm512_andnot_si512(_mm512_or_si512(B0, B1), a[z]); any = _mm512_or_si512(any, a[z]);
        }
        if (!_mm512_test_epi64_mask(any, any)) return 0;
    }
    for (; i < iend; i++) {
        const uint32_t e0 = CVEZ(i), v0 = e0 & VM; const uint8_t *p0 = AR + (e0 >> VB); const int Z0 = (int)(v0 >> 9);
        const __m512i ix0 = OPT_IDX(v0), m0 = _mm512_set1_epi64((long long)AFF[v0 & 7]); __m512i any = _mm512_setzero_si512();
        for (int z = 0; z < nz; z++) { a[z] = _mm512_andnot_si512(_mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix0, _mm512_loadu_si512((const void *)(p0 + ((size_t)(z ^ Z0) << 6)))), m0, 0), a[z]); any = _mm512_or_si512(any, a[z]); }
        if (!_mm512_test_epi64_mask(any, any)) return 0;
    }
#undef CVEZ
    for (int z = 0; z < nz; z++) _mm512_store_si512((void *)(w + 8 * z), a[z]);
    return 1;
}
static void search_fast(int t) {''')
else:
    rep('    __m256i a[4];\n    for (int z = 0; z < nblk; z++) a[z] = _mm256_load_si256((const __m256i *)(L->allm + 4 * z));',
        '    __m256i a[16];\n    for (int z = 0; z < nblk; z++) a[z] = _mm256_load_si256((const __m256i *)(L->allm + 4 * z));')
    rep('    if (kt >= 8) return kt == 8 ? filter_blk(L, S, w, 1, 9) : kt == 9 ? filter_blk(L, S, w, 2, 9) : filter_blk(L, S, w, 4, 10);',
        '    if (kt >= 8) return kt == 8 ? filter_blk(L, S, w, 1, 9) : kt == 9 ? filter_blk(L, S, w, 2, 9) : kt == 10 ? filter_blk(L, S, w, 4, 10)\n                      : kt == 11 ? filter_blk(L, S, w, 8, 11) : filter_blk(L, S, w, 16, 12);')
    rep('    if (OPT_ARENA && L->vec && L->kt <= 10 && (L->ntr == 0 || L->CVL)) r = filter_arena(L, S, w);',
        '    if (OPT_ARENA && L->vec && L->kt <= 12 && L->arena) r = filter_arena(L, S, w);')
open(dst, 'w').write(s)
print('patched', dst)
