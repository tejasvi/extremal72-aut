/* rglue.c -- c3explore independent re-classification, stage 2 (written independently of c3class's frames.c).
   For each E_B class (Hermitian self-orthogonal [NB, KB, >= D] code, n = NB + D, KB = n/2 - D + 1) enumerate the
   codes E = <e1> + E_B + {(x, phi(x))} with e1 = 1^D on S1 = {0..D-1}: phi^{-1} is given on a basis W_0..W_{M-1}
   of V2 = E_B^perp / E_B (M = D - 2) by x_j in V8 = 1^perp / <1> (inside F4^D).  Conditions: Gram
   <x_i,x_j> = <W_i,W_j>, and m8(s) + m16(t) >= D for every nonzero combination (t on the B side, s = phi^{-1}(t);
   m8, m16 = minimum weights of the classes), which is exactly d(E) >= D.
   Orderly: G = S_D x F4^* acts on the D side; x_j is taken minimal in its orbit under the stabiliser of
   x_0..x_{j-1}, so each G-orbit of valid tuples is visited exactly once; N_phi += |G| / |Stab(tuple)| counts all
   glue maps (weighted double count check).
   Acceptance (one or more representatives per code): supp(e1) must have the lexicographically smallest
   intersection profile (n_0..n_D; n_k = number of other weight-D supports meeting it in k points) among all
   weight-D supports of E (an invariant of (E, supp e1) under monomial maps and conjugation).
   Accepted codes: own class key (mycanon2.h, word set = all weight-D words, or all words of weight <= D+2j if
   those do not span), deduplicated per E_B; for each new one also c3class's key (cform.h via ckey.c).
   Usage: rglue NB D EBFILE OUTFILE [PART NPARTS]     (EBFILE lines: KEYHEX aut sc ... as written by ebcls2;
          env EBOFF = global index of the file's first line, added to the printed E_B index; a token id=<i>
          on the line overrides the index)
   Output OUTFILE:      A myhash myaut mysc A_D cfkey cfaut cfsc ebidx
          OUTFILE.eb:   B ebidx ebaut ebsc leaves nphi accepted distinct nodes secs
   Env: DEBUGW=1 checks every accepted code by full enumeration (self-orthogonality, d, A_D).
        CFCHECK=1 also computes cform's key through its own canon_code (word enumeration) and compares. */
#include "mycanon2.h"
#include <time.h>
int c3c_class_key(const unsigned *lo, const unsigned *hi, int k, int n, int d, unsigned *klo, unsigned *khi,
                  double *aut, int *sc);
int c3c_class_key_wl(const unsigned *lo, const unsigned *hi, int k, int n, const unsigned *wlo, const unsigned *whi,
                     long nw, unsigned *klo, unsigned *khi, double *aut, int *sc);
static int cfcheck;
static int D, NB, N, K, KB, M, Q;
/* ---- D side ---- */
static vec v8rep[4096], v8lift[4096][4];
static unsigned char wt8[4096][4], m8[4096], norm8[4096];
static int mulq[4][4096], orbmin[4096];
static unsigned char perms[40320][8]; static int nperm, ngrp;
static inline int gact(int g, int idx) {
    const unsigned char *s = perms[g / 3]; int lam = g % 3 + 1;
    int v[8], w[8] = {0}, sum = 0, t = idx;
    for (int i = 0; i < M; i++) { v[i] = t & 3; t >>= 2; sum ^= v[i]; }
    v[M] = sum; v[D - 1] = 0;
    for (int j = 0; j < D; j++) w[s[j]] = f4mul[lam][v[j]];
    int r = 0; for (int i = M - 1; i >= 0; i--) r = r * 4 + (w[i] ^ w[D - 1]);
    return r;
}
/* ---- B side ---- */
static vec EB[8], W[8], cvec[4096]; static int H16[8][8];
static unsigned char m16[4096];
static int cl_off[4096][10]; static vec *cl_v;          /* coset vectors of weight w in [0, D-2]: cl_off[t][w]..[w+1] */
static u32 ebsup[1100]; static int nebsup;              /* weight-D words of E_B, projective */
/* ---- DFS state ---- */
typedef struct { int c, a, thr; } cons_t;
static cons_t *cons[8]; static int ncons[8];
static int xs[8], *p8[9], *cand[9][8], ncand[9][8], *Hst[9], nH[9];
static long nodes[9], nleaves, nphi, nacc, ndist;
static FILE *fo; static long ebidx; static int debugw;
/* per-E_B dedupe of own keys (128-bit hashes) */
#define HT_BITS 22
static unsigned long long *ht_a, *ht_b; static long ht_n; static int ht_gen;
static unsigned char *ht_stamp;
static int ht_insert(unsigned long long a, unsigned long long b) {
    unsigned long long mask = (1ULL << HT_BITS) - 1, h = (a ^ (b * 0x9E3779B97F4A7C15ULL)) & mask;
    while (ht_stamp[h] == ht_gen) { if (ht_a[h] == a && ht_b[h] == b) return 0; h = (h + 1) & mask; }
    ht_stamp[h] = ht_gen; ht_a[h] = a; ht_b[h] = b; ht_n++;
    if (ht_n > (long)(mask >> 1)) { fprintf(stderr, "hash table full\n"); exit(5); }
    return 1;
}
static void key_hash(const vec *key, int k, unsigned long long *ha, unsigned long long *hb) {
    unsigned long long a = 0xcbf29ce484222325ULL, b = 0x84222325cbf29ce4ULL;
    for (int r = 0; r < k; r++) {
        a ^= key[r].lo; a *= 0x100000001b3ULL; a ^= a >> 29; a ^= key[r].hi; a *= 0x100000001b3ULL; a ^= a >> 29;
        b += key[r].lo * 0x9E3779B97F4A7C15ULL; b ^= b >> 31; b *= 0xBF58476D1CE4E5B9ULL; b += key[r].hi; b ^= b >> 27; b *= 0x94D049BB133111EBULL;
    }
    *ha = a; *hb = b;
}
/* all words of weight <= wmax (and >= 1) of the code by Gray code over the F2-basis {g, w g} */
static long words_upto(const vec *gen, int k, int wmax, vec **out) {
    vec B[32]; int mm = 0; for (int i = 0; i < k; i++) { B[mm++] = gen[i]; B[mm++] = vmulw(gen[i]); }
    long cap = 1 << 16, n = 0; vec *L = malloc(sizeof(vec) * cap); vec cur = {0, 0};
    for (u64 g = 1; g < (1ULL << mm); g++) { cur = vadd(cur, B[__builtin_ctzll(g)]); if (vwt(cur) <= wmax) { if (n == cap) { cap *= 2; L = realloc(L, sizeof(vec) * cap); } L[n++] = cur; } }
    *out = L; return n;
}
static int rank_of(const vec *L, long n, int k) {
    vec B[32]; int pc[32], r = 0;          /* B[i]: pivot pc[i] (value 1), zero at pc[j] for j < i */
    for (long j = 0; j < n && r < k; j++) {
        vec x = L[j];
        for (int i = 0; i < r; i++) { int c = vget(x, pc[i]); if (c) x = vadd(x, vscal(c, B[i])); }
        if (!vsupp(x)) continue;
        int p = __builtin_ctz(vsupp(x)); B[r] = vscal(f4inv[vget(x, p)], x); pc[r++] = p;
    }
    return r;
}
static void accept_code(int ns) {
    vec gen[16]; int r = 0;
    gen[r].lo = (1u << D) - 1; gen[r].hi = 0; r++;
    for (int i = 0; i < KB; i++) { gen[r].lo = EB[i].lo << D; gen[r].hi = EB[i].hi << D; r++; }
    for (int j = 0; j < M; j++) { gen[r].lo = v8rep[xs[j]].lo | (W[j].lo << D); gen[r].hi = v8rep[xs[j]].hi | (W[j].hi << D); r++; }
    /* weight-D words (all scalar multiples) */
    long cap = 4 * (long)ns + 16, nw = 0; vec *WL = malloc(sizeof(vec) * cap);
    for (int l = 1; l <= 3; l++) WL[nw++] = vscal(l, gen[0]);
    {   vec ebw[1024]; combos(EB, KB, ebw);
        for (int i = 1; i < (1 << (2 * KB)); i++) if (vwt(ebw[i]) == D) { vec v = { ebw[i].lo << D, ebw[i].hi << D }; WL[nw++] = v; } }
    for (int t = 1; t < Q; t++) {
        int s = p8[M][t]; if (m8[s] + m16[t] != D) continue;
        for (int l = 0; l < 4; l++) { int need = D - wt8[s][l]; if (need < 0 || need > D - 2) continue;
            for (int q = cl_off[t][need]; q < cl_off[t][need + 1]; q++) {
                vec v = { v8lift[s][l].lo | (cl_v[q].lo << D), v8lift[s][l].hi | (cl_v[q].hi << D) };
                if (nw == cap) { cap *= 2; WL = realloc(WL, sizeof(vec) * cap); } WL[nw++] = v; } }
    }
    if (nw != 3 * (long)ns) { fprintf(stderr, "word list %ld != 3*%d\n", nw, ns); exit(6); }
    if (debugw) {
        /* self-orthogonality and full weight check */
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (vherm(gen[i], gen[j])) { fprintf(stderr, "DEBUGW: not s.o.\n"); exit(7); }
        vec tmp[16]; memcpy(tmp, gen, sizeof tmp); int pv[16]; if (vrref(tmp, K, N, pv) != K) { fprintf(stderr, "DEBUGW: rank\n"); exit(7); }
        vec *L; long n2 = words_upto(gen, K, D, &L); long cntD = 0;
        for (long j = 0; j < n2; j++) { if (vwt(L[j]) < D) { fprintf(stderr, "DEBUGW: weight %d word\n", vwt(L[j])); exit(7); } cntD++; }
        free(L);
        if (cntD != nw) { fprintf(stderr, "DEBUGW: A_D %ld vs %ld\n", cntD, nw); exit(7); }
    }
    vec key[16]; double myaut; int mysc; int spans = rank_of(WL, nw, K) == K;
    if (spans) mc_class_wl(gen, K, N, WL, nw, key, &myaut, &mysc);
    else {
        int wmax = D + 2; vec *L; long n2;
        for (;;) { n2 = words_upto(gen, K, wmax, &L); if (rank_of(L, n2, K) == K) break; free(L); wmax += 2; }
        mc_class_wl(gen, K, N, L, n2, key, &myaut, &mysc); free(L);
    }
    nacc++;
    unsigned long long ha, hb; key_hash(key, K, &ha, &hb);
    if (!ht_insert(ha, hb)) { free(WL); return; }
    ndist++;
    unsigned lo[16], hi[16], klo[16], khi[16]; double cfaut; int cfsc;
    for (int i = 0; i < K; i++) { lo[i] = gen[i].lo; hi[i] = gen[i].hi; }
    if (spans) {   /* cform's word set = all weight-D words: pass it directly */
        unsigned *wlo = malloc(sizeof(unsigned) * nw), *whi = malloc(sizeof(unsigned) * nw);
        for (long j = 0; j < nw; j++) { wlo[j] = WL[j].lo; whi[j] = WL[j].hi; }
        if (c3c_class_key_wl(lo, hi, K, N, wlo, whi, nw, klo, khi, &cfaut, &cfsc)) { fprintf(stderr, "cform_wl failed\n"); exit(8); }
        free(wlo); free(whi);
        if (cfcheck) {
            unsigned klo2[16], khi2[16]; double a2; int s2;
            if (c3c_class_key(lo, hi, K, N, D, klo2, khi2, &a2, &s2)) { fprintf(stderr, "cform failed\n"); exit(8); }
            if (memcmp(klo, klo2, sizeof(unsigned) * K) || memcmp(khi, khi2, sizeof(unsigned) * K) || a2 != cfaut || s2 != cfsc) { fprintf(stderr, "CFCHECK MISMATCH E_B %ld\n", ebidx); exit(9); }
        }
    } else if (c3c_class_key(lo, hi, K, N, D, klo, khi, &cfaut, &cfsc)) { fprintf(stderr, "cform failed\n"); exit(8); }
    free(WL);
    fprintf(fo, "A %016llx%016llx %.0f %d %d ", ha, hb, myaut, mysc, 3 * ns);
    for (int i = 0; i < K; i++) fprintf(fo, "%08x%08x", klo[i], khi[i]);
    fprintf(fo, " %.0f %d %ld\n", cfaut, cfsc, ebidx);
}
static u32 sup[4096];
static void leaf(void) {
    nleaves++; nphi += ngrp / nH[M];
    int ns = 0; sup[ns++] = (1u << D) - 1;
    for (int i = 0; i < nebsup; i++) sup[ns++] = ebsup[i];
    for (int t = 1; t < Q; t++) {
        int tt = t; while (!(tt & 3)) tt >>= 2; if ((tt & 3) != 1) continue;          /* projective: lowest digit 1 */
        int s = p8[M][t]; if (m8[s] + m16[t] != D) continue;
        for (int l = 0; l < 4; l++) { int need = D - wt8[s][l]; if (need < 0 || need > D - 2) continue;
            u32 s8 = vsupp(v8lift[s][l]);
            for (int q = cl_off[t][need]; q < cl_off[t][need + 1]; q++) sup[ns++] = s8 | (vsupp(cl_v[q]) << D); }
    }
    /* n_0 for all supports; reject if some support has fewer disjoint supports than e1 */
    static int n0[4096];
    for (int i = 0; i < ns; i++) n0[i] = 0;
    for (int i = 0; i < ns; i++) for (int j = i + 1; j < ns; j++) if (!(sup[i] & sup[j])) { n0[i]++; n0[j]++; }
    for (int i = 1; i < ns; i++) if (n0[i] < n0[0]) return;
    int p1[33] = {0};
    for (int j = 1; j < ns; j++) p1[__builtin_popcount(sup[0] & sup[j])]++;
    for (int i = 1; i < ns; i++) if (n0[i] == n0[0]) {
        int p[33] = {0};
        for (int j = 0; j < ns; j++) if (j != i) p[__builtin_popcount(sup[i] & sup[j])]++;
        for (int k = 0; k <= D; k++) { if (p[k] < p1[k]) return; if (p[k] > p1[k]) break; }
    }
    accept_code(ns);
}
static void dfs(int lev) {
    nodes[lev]++;
    if (lev == M) { leaf(); return; }
    int ya[4]; ya[0] = 0;
    int *H2 = Hst[lev + 1];
    for (int ci = 0; ci < ncand[lev][lev]; ci++) {
        int y = cand[lev][lev][ci];
        ya[1] = y; ya[2] = mulq[2][y]; ya[3] = mulq[3][y];
        int ok = 1; const int *P = p8[lev];
        for (int q = 0; q < ncons[lev]; q++) { const cons_t *c = &cons[lev][q]; if (m8[P[c->c] ^ ya[c->a]] < c->thr) { ok = 0; break; } }
        if (!ok) continue;
        int n2 = 0;
        if (lev == 0) {
            if (orbmin[y] != y) continue;
            for (int h = 0; h < ngrp; h++) if (gact(h, y) == y) H2[n2++] = h;
        } else {
            int rep = 1;
            for (int hh = 0; hh < nH[lev]; hh++) { int h = Hst[lev][hh]; int z = gact(h, y); if (z < y) { rep = 0; break; } if (z == y) H2[n2++] = h; }
            if (!rep) continue;
        }
        nH[lev + 1] = n2; xs[lev] = y;
        int sz = 1; for (int i = 0; i < lev; i++) sz *= 4;
        for (int c = 0; c < sz; c++) { int b = P[c]; p8[lev + 1][c] = b; p8[lev + 1][c + sz] = b ^ ya[1]; p8[lev + 1][c + 2 * sz] = b ^ ya[2]; p8[lev + 1][c + 3 * sz] = b ^ ya[3]; }
        vec yv = v8rep[y];
        for (int L = lev + 1; L < M; L++) { int n3 = 0; int h = H16[lev][L];
            for (int q = 0; q < ncand[lev][L]; q++) { int z = cand[lev][L][q]; if (vherm(yv, v8rep[z]) == h) cand[lev + 1][L][n3++] = z; }
            ncand[lev + 1][L] = n3; }
        dfs(lev + 1);
    }
}
static int cons_cmp(const void *a, const void *b) { const cons_t *x = a, *y = b; return y->thr - x->thr; }
/* ---- setup per E_B ---- */
static int setup_eb(void) {
    /* E_B words, dual, V2 basis */
    vec eb[8]; memcpy(eb, EB, sizeof(vec) * KB); int pv[8];
    if (vrref(eb, KB, NB, pv) != KB) return -1;
    memcpy(EB, eb, sizeof(vec) * KB);
    for (int i = 0; i < KB; i++) for (int j = 0; j < KB; j++) if (vherm(EB[i], EB[j])) return -2;
    vec ebw[1024]; combos(EB, KB, ebw); int neb = 1 << (2 * KB);
    vec perp[32]; int np = 0; u32 pm = 0; for (int k = 0; k < KB; k++) pm |= 1u << pv[k];
    for (int j = 0; j < NB; j++) if (!((pm >> j) & 1)) { vec x = {0, 0}; vset(&x, j, 1); for (int k = 0; k < KB; k++) vset(&x, pv[k], f4conj[vget(EB[k], j)]); perp[np++] = x; }
    /* initial complement of E_B in perp, then greedy low-weight basis of V2 (pruning order only) */
    vec Wi[8]; int nwi = 0;
    for (int j = 0; j < np && nwi < M; j++) { vec T[16]; int k2 = 0; for (int k = 0; k < KB; k++) T[k2++] = EB[k]; for (int k = 0; k < nwi; k++) T[k2++] = Wi[k]; T[k2++] = perp[j]; int pp[16]; if (vrref(T, k2, NB, pp) == k2) Wi[nwi++] = perp[j]; }
    if (nwi != M) return -3;
    static int mwi[4096], ordi[4096];
    for (int idx = 0; idx < Q; idx++) { vec x = {0, 0}; int t = idx; for (int i = 0; i < M; i++) { int d = t & 3; t >>= 2; if (d) x = vadd(x, vscal(d, Wi[i])); }
        int mw = 99; for (int k = 0; k < neb; k++) { int w = vwt(vadd(x, ebw[k])); if (w < mw) mw = w; } mwi[idx] = mw; ordi[idx] = idx; }
    for (int i = 1; i < Q; i++) { int v = ordi[i], j = i - 1; while (j >= 0 && mwi[ordi[j]] > mwi[v]) { ordi[j + 1] = ordi[j]; j--; } ordi[j + 1] = v; }
    int nw = 0;
    for (int ii = 1; ii < Q && nw < M; ii++) { int idx = ordi[ii]; vec x = {0, 0}; int t = idx; for (int i = 0; i < M; i++) { int d = t & 3; t >>= 2; if (d) x = vadd(x, vscal(d, Wi[i])); }
        vec T[16]; int k2 = 0; for (int k = 0; k < KB; k++) T[k2++] = EB[k]; for (int k = 0; k < nw; k++) T[k2++] = W[k]; T[k2++] = x; int pp[16];
        if (vrref(T, k2, NB, pp) == k2) W[nw++] = x; }
    if (nw != M) return -4;
    for (int i = 0; i < M; i++) for (int j = 0; j < M; j++) H16[i][j] = vherm(W[i], W[j]);
    /* classes t: min weight, coset vectors of weight <= D-2 */
    static int cnt[4096][10];
    long tot = 0;
    for (int t = 0; t < Q; t++) { vec x = {0, 0}; int tt = t; for (int i = 0; i < M; i++) { int d = tt & 3; tt >>= 2; if (d) x = vadd(x, vscal(d, W[i])); } cvec[t] = x;
        for (int w = 0; w < 10; w++) cnt[t][w] = 0;
        int mw = 99; for (int k = 0; k < neb; k++) { int w = vwt(vadd(x, ebw[k])); if (w < mw) mw = w; if (w <= D - 2) cnt[t][w]++; }
        m16[t] = mw; for (int w = 0; w <= D - 2; w++) tot += cnt[t][w]; }
    free(cl_v); cl_v = malloc(sizeof(vec) * (tot + 1)); long off = 0;
    for (int t = 0; t < Q; t++) {
        for (int w = 0; w <= D - 1; w++) { cl_off[t][w] = off; if (w <= D - 2) off += cnt[t][w]; }
        int fill[10]; for (int w = 0; w <= D - 2; w++) fill[w] = cl_off[t][w];
        for (int k = 0; k < neb; k++) { vec y = vadd(cvec[t], ebw[k]); int w = vwt(y); if (w <= D - 2) cl_v[fill[w]++] = y; }
    }
    nebsup = 0;
    for (int k = 1; k < neb; k++) if (vwt(ebw[k]) == D) { int f = __builtin_ctz(vsupp(ebw[k])); if (vget(ebw[k], f) == 1) ebsup[nebsup++] = vsupp(ebw[k]) << D; }
    /* constraint lists */
    for (int lev = 0; lev < M; lev++) {
        int sz = 1; for (int i = 0; i < lev; i++) sz *= 4;
        free(cons[lev]); cons[lev] = malloc(sizeof(cons_t) * 3 * sz); ncons[lev] = 0;
        for (int a = 1; a <= 3; a++) for (int c = 0; c < sz; c++) { int t = c + a * sz; int thr = D - m16[t]; if (thr < 1) thr = 1; cons_t z = { c, a, thr }; cons[lev][ncons[lev]++] = z; }
        qsort(cons[lev], ncons[lev], sizeof(cons_t), cons_cmp);
    }
    /* level-0 candidate lists */
    for (int L = 0; L < M; L++) { int n3 = 0; for (int y = 0; y < Q; y++) if (norm8[y] == H16[L][L]) cand[0][L][n3++] = y; ncand[0][L] = n3; }
    p8[0][0] = 0;
    return 0;
}
static int uf_find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: rglue NB D EBFILE OUTFILE [PART NPARTS]\n"); return 1; }
    NB = atoi(argv[1]); D = atoi(argv[2]); N = NB + D; K = N / 2; KB = K - D + 1; M = D - 2;
    Q = 1; for (int i = 0; i < M; i++) Q *= 4;
    if (NB - 2 * KB != M || D > 8 || N > 32) { fprintf(stderr, "bad parameters\n"); return 1; }
    int part = argc > 6 ? atoi(argv[5]) : 0, nparts = argc > 6 ? atoi(argv[6]) : 1;
    debugw = getenv("DEBUGW") != NULL; cfcheck = getenv("CFCHECK") != NULL;
    /* D side tables */
    for (int idx = 0; idx < Q; idx++) {
        vec u = {0, 0}; int t = idx, sum = 0;
        for (int i = 0; i < M; i++) { int d = t & 3; t >>= 2; vset(&u, i, d); sum ^= d; }
        vset(&u, M, sum); v8rep[idx] = u;
        vec one = { (1u << D) - 1, 0 }; int mw = 99;
        for (int l = 0; l < 4; l++) { vec y = vadd(u, vscal(l, one)); v8lift[idx][l] = y; wt8[idx][l] = vwt(y); if (vwt(y) < mw) mw = vwt(y); }
        m8[idx] = mw; norm8[idx] = vherm(u, u);
        for (int l = 0; l < 4; l++) { int r = 0, tt = idx; int dg[8]; for (int i = 0; i < M; i++) { dg[i] = tt & 3; tt >>= 2; } for (int i = M - 1; i >= 0; i--) r = r * 4 + f4mul[l][dg[i]]; mulq[l][idx] = r; }
    }
    { int p[8]; for (int i = 0; i < D; i++) p[i] = i; nperm = 0;
      for (;;) { for (int i = 0; i < D; i++) perms[nperm][i] = p[i]; nperm++;
        int i = D - 2; while (i >= 0 && p[i] > p[i + 1]) i--; if (i < 0) break; int j = D - 1; while (p[j] < p[i]) j--; int t = p[i]; p[i] = p[j]; p[j] = t;
        for (int a = i + 1, b = D - 1; a < b; a++, b--) { t = p[a]; p[a] = p[b]; p[b] = t; } }
      ngrp = nperm * 3; }
    /* orbits of G on V8 classes by generators (find group elements for (0 1), (0 1 .. D-1), omega) */
    { int gidx[3] = { -1, -1, -1 };
      for (int g = 0; g < nperm; g++) {
          int istr = 1, iscyc = 1;
          for (int j = 0; j < D; j++) { int tj = j == 0 ? 1 : j == 1 ? 0 : j; if (perms[g][j] != tj) istr = 0; if (perms[g][j] != (j + 1) % D) iscyc = 0; }
          if (istr) gidx[0] = 3 * g;
          if (iscyc) gidx[1] = 3 * g; }
      gidx[2] = 1;   /* identity permutation (index 0) with lambda = w */
      static int par[4096]; for (int y = 0; y < Q; y++) par[y] = y;
      for (int y = 0; y < Q; y++) for (int k = 0; k < 3; k++) { int z = gact(gidx[k], y); int a = uf_find(par, y), b = uf_find(par, z); if (a != b) { if (a < b) par[b] = a; else par[a] = b; } }
      for (int y = 0; y < Q; y++) orbmin[y] = uf_find(par, y);   /* union by smaller root: root = orbit minimum */
    }
    for (int l = 0; l <= M; l++) { int sz = 1; for (int i = 0; i < l; i++) sz *= 4; p8[l] = malloc(sizeof(int) * sz); Hst[l] = malloc(sizeof(int) * ngrp); }
    for (int l = 0; l <= M; l++) for (int L = 0; L < M; L++) cand[l][L] = malloc(sizeof(int) * Q);
    ht_a = malloc(sizeof(unsigned long long) << HT_BITS); ht_b = malloc(sizeof(unsigned long long) << HT_BITS);
    ht_stamp = calloc(1, 1 << HT_BITS);
    FILE *fe = fopen(argv[3], "r"); if (!fe) { perror("ebfile"); return 2; }
    fo = fopen(argv[4], "w"); if (!fo) { perror("out"); return 2; }
    char ebname[4096]; snprintf(ebname, sizeof ebname, "%s.eb", argv[4]); FILE *fb = fopen(ebname, "w"); if (!fb) { perror("eb out"); return 2; }
    char line[4096]; long li = -1; long eboff = getenv("EBOFF") ? atol(getenv("EBOFF")) : 0;
    while (fgets(line, sizeof line, fe)) {
        li++; if (li % nparts != part) continue;
        ebidx = li + eboff;
        char *q = line;
        for (int r = 0; r < KB; r++) { char h1[9], h2[9]; memcpy(h1, q, 8); h1[8] = 0; memcpy(h2, q + 8, 8); h2[8] = 0; q += 16; EB[r].lo = strtoul(h1, NULL, 16); EB[r].hi = strtoul(h2, NULL, 16); }
        double ebaut = 0; int ebsc = 0; sscanf(q, "%lf %d", &ebaut, &ebsc);
        { char *idp = strstr(q, "id="); if (idp) ebidx = atol(idp + 3); }
        clock_t t0 = clock();
        int rc = setup_eb(); if (rc) { fprintf(stderr, "E_B %ld setup failed %d\n", li, rc); return 3; }
        for (int l = 0; l <= M; l++) nodes[l] = 0;
        nleaves = nphi = nacc = ndist = 0; ht_gen++; ht_n = 0;
        if (ht_gen == 256) { memset(ht_stamp, 0, 1 << HT_BITS); ht_gen = 1; }
        nH[0] = ngrp;
        dfs(0);
        long nn = 0; for (int l = 0; l <= M; l++) nn += nodes[l];
        fprintf(fb, "B %ld %.0f %d %ld %ld %ld %ld %ld %.2f\n", ebidx, ebaut, ebsc, nleaves, nphi, nacc, ndist, nn, (double)(clock() - t0) / CLOCKS_PER_SEC);
        fflush(fb); fflush(fo);
    }
    fclose(fo); fclose(fb);
    return 0;
}
