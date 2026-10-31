/* Independent glue-map counter (auditor code, rev_reclass).  For an E_B ([16,5,>=8] Hermitian s.o., 5 hex rows
   "%08x%08x" lo/hi as in ebcls2 output) count ALL isometries psi: V2 = E_B^perp/E_B -> V8 = 1^perp/<1> (F4^8)
   with m8(psi(t)) + m16(t) >= 8 for all t != 0 (and psi injective), where m8, m16 = min weights of classes.
   Symmetry used only for the first basis image: N = sum over G-orbit reps y of |orbit(y)| * #completions(y),
   G = S8 x F4^* (computed by explicit enumeration of all 120960 elements).  Completions counted by plain DFS.
   Also counts, per N_phi, nothing else.  usage: gcount FILE LINE_INDEX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32;
static int MUL[4][4], INV[4], CONJ[4];
static void init_field(void) {
    for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) {
        int a = x & 1, b = x >> 1, c = y & 1, d = y >> 1;
        MUL[x][y] = ((a & c) ^ (b & d)) | (((a & d) ^ (b & c) ^ (b & d)) << 1);
    }
    for (int x = 1; x < 4; x++) for (int y = 1; y < 4; y++) if (MUL[x][y] == 1) INV[x] = y;
    for (int x = 0; x < 4; x++) CONJ[x] = MUL[x][x];
}
typedef struct { u32 lo, hi; } bv;
static int NB = 16;
static inline int get(bv v, int i) { return ((v.lo >> i) & 1) | (((v.hi >> i) & 1) << 1); }
static inline void put(bv *v, int i, int c) { v->lo = (v->lo & ~(1u << i)) | ((u32)(c & 1) << i); v->hi = (v->hi & ~(1u << i)) | ((u32)(c >> 1) << i); }
static inline bv add(bv a, bv b) { bv r = { a.lo ^ b.lo, a.hi ^ b.hi }; return r; }
static bv smul(int c, bv a) { bv r = {0, 0}; for (int i = 0; i < 32; i++) { int x = get(a, i); if (x) put(&r, i, MUL[c][x]); } return r; }
static inline int wt(bv a) { return __builtin_popcount(a.lo | a.hi); }
static int herm(bv a, bv b, int n) { int s = 0; for (int i = 0; i < n; i++) s ^= MUL[get(a, i)][CONJ[get(b, i)]]; return s; }
static int rank_of(const bv *g, int k, int n) {
    bv m[40]; memcpy(m, g, sizeof(bv) * k); int r = 0;
    for (int col = 0; col < n && r < k; col++) {
        int s = -1; for (int i = r; i < k; i++) if (get(m[i], col)) { s = i; break; }
        if (s < 0) continue;
        bv t = m[s]; m[s] = m[r]; m[r] = t; m[r] = smul(INV[get(m[r], col)], m[r]);
        for (int i = 0; i < k; i++) if (i != r) { int c = get(m[i], col); if (c) m[i] = add(m[i], smul(c, m[r])); }
        r++;
    }
    return r;
}
/* V8: class of u in 1^perp (F4^8) mod <1>; representative with u_0 = 0; index = digits of u_1..u_6 (u_7 = sum) */
#define Q 4096
static bv v8[Q]; static int m8v[Q];
static int v8index(bv u) {     /* u in 1^perp; normalise u_0 = 0 */
    int c0 = get(u, 0); int idx = 0;
    for (int i = 1; i <= 6; i++) idx |= (get(u, i) ^ c0) << (2 * (i - 1));
    return idx;
}
static int m16v[Q]; static int H[6][6]; static bv U[6];
static int x[6]; static int *cand[6]; static int ncand[6];
static int s_of[7][Q];      /* s_of[j][c] = psi(sum_{i<j} c_i U_i) as V8 index, c < 4^j */

static long long ncomp;
static inline int h8(int a, int b) { return herm(v8[a], v8[b], 8); }
static void dfs(int j) {
    if (j == 6) { ncomp++; return; }
    int sz = 1 << (2 * j);
    for (int ci = 0; ci < ncand[j]; ci++) {
        int z = cand[j][ci];
        int ok = 1;
        for (int i = 0; i < j && ok; i++) if (h8(x[i], z) != H[i][j]) ok = 0;
        if (!ok) continue;
        for (int a = 1; a <= 3 && ok; a++) {
            int za = 0; for (int i = 0; i < 6; i++) za |= MUL[a][(z >> (2 * i)) & 3] << (2 * i);
            for (int c = 0; c < sz; c++) {
                int t = c + a * sz, s = s_of[j][c] ^ za;
                if (s == 0 || m8v[s] + m16v[t] < 8) { ok = 0; break; }
            }
        }
        if (!ok) continue;
        x[j] = z;
        for (int a = 0; a <= 3; a++) { int za = 0; for (int i = 0; i < 6; i++) za |= MUL[a][(z >> (2 * i)) & 3] << (2 * i);
            for (int c = 0; c < sz; c++) s_of[j + 1][c + a * sz] = s_of[j][c] ^ za; }
        dfs(j + 1);
    }
}
int main(int argc, char **argv) {
    init_field();
    FILE *f = fopen(argv[1], "r"); long want = atol(argv[2]); char line[8192]; long li = -1;
    while (fgets(line, sizeof line, f)) { li++; if (li == want) break; }
    if (li != want) { fprintf(stderr, "no line\n"); return 2; }
    bv E[5]; char *q = line;
    for (int r = 0; r < 5; r++) { char h[9]; memcpy(h, q, 8); h[8] = 0; E[r].lo = strtoul(h, 0, 16); memcpy(h, q + 8, 8); h[8] = 0; E[r].hi = strtoul(h, 0, 16); q += 16; }
    if (rank_of(E, 5, 16) != 5) { fprintf(stderr, "rank\n"); return 3; }
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) if (herm(E[i], E[j], 16)) { fprintf(stderr, "not so\n"); return 3; }
    bv cw[1024]; for (int t = 0; t < 1024; t++) { bv y = {0, 0}; for (int j = 0; j < 5; j++) { int c = (t >> (2 * j)) & 3; if (c) y = add(y, smul(c, E[j])); } cw[t] = y; }
    for (int t = 1; t < 1024; t++) if (wt(cw[t]) < 8) { fprintf(stderr, "weight\n"); return 3; }
    /* E_B^perp: null space of conj(E) */
    bv A[5]; for (int r = 0; r < 5; r++) { bv y = {0, 0}; for (int i = 0; i < 16; i++) put(&y, i, CONJ[get(E[r], i)]); A[r] = y; }
    int piv[5], rr = 0;
    for (int col = 0; col < 16 && rr < 5; col++) {
        int s = -1; for (int i = rr; i < 5; i++) if (get(A[i], col)) { s = i; break; }
        if (s < 0) continue;
        bv t = A[s]; A[s] = A[rr]; A[rr] = t; A[rr] = smul(INV[get(A[rr], col)], A[rr]);
        for (int i = 0; i < 5; i++) if (i != rr) { int c = get(A[i], col); if (c) A[i] = add(A[i], smul(c, A[rr])); }
        piv[rr++] = col;
    }
    int isp[16] = {0}; for (int i = 0; i < rr; i++) isp[piv[i]] = 1;
    bv P[16]; int np = 0;
    for (int j = 15; j >= 0; j--) if (!isp[j]) { bv y = {0, 0}; put(&y, j, 1); for (int i = 0; i < rr; i++) put(&y, piv[i], get(A[i], j)); P[np++] = y; }
    for (int t = 0; t < np; t++) for (int r = 0; r < 5; r++) if (herm(P[t], E[r], 16)) { fprintf(stderr, "perp\n"); return 4; }
    /* complement of E_B in E_B^perp: choose greedily among ALL classes by (min weight descending?) -- use an
       ordering different from rglue: classes of the initial complement sorted by m16 ascending, ties by index desc */
    bv cur[16]; int nc = 0; for (int r = 0; r < 5; r++) cur[nc++] = E[r];
    bv Wi[6]; int nwi = 0;
    for (int t = 0; t < np && nwi < 6; t++) { cur[nc] = P[t]; if (rank_of(cur, nc + 1, 16) == nc + 1) { nc++; Wi[nwi++] = P[t]; } }
    if (nwi != 6) { fprintf(stderr, "dim\n"); return 4; }
    static int mw0[Q], ord[Q];
    for (int t = 0; t < Q; t++) { bv y = {0, 0}; for (int j = 0; j < 6; j++) { int c = (t >> (2 * j)) & 3; if (c) y = add(y, smul(c, Wi[j])); }
        int mw = 99; for (int k = 0; k < 1024; k++) { int w = wt(add(y, cw[k])); if (w < mw) mw = w; } mw0[t] = mw; ord[t] = t; }
    for (int i = 1; i < Q; i++) { int v = ord[i], j = i - 1; while (j >= 0 && (mw0[ord[j]] > mw0[v] || (mw0[ord[j]] == mw0[v] && ord[j] < v))) { ord[j + 1] = ord[j]; j--; } ord[j + 1] = v; }
    nc = 5; for (int r = 0; r < 5; r++) cur[r] = E[r];
    int nu = 0;
    for (int ii = 0; ii < Q && nu < 6; ii++) { int t = ord[ii]; if (!t) continue; bv y = {0, 0}; for (int j = 0; j < 6; j++) { int c = (t >> (2 * j)) & 3; if (c) y = add(y, smul(c, Wi[j])); }
        cur[nc] = y; if (rank_of(cur, nc + 1, 16) == nc + 1) { nc++; U[nu++] = y; } }
    if (nu != 6) { fprintf(stderr, "dimU\n"); return 4; }
    for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) H[i][j] = herm(U[i], U[j], 16);
    int hist16[20] = {0};
    for (int t = 0; t < Q; t++) { bv y = {0, 0}; for (int j = 0; j < 6; j++) { int c = (t >> (2 * j)) & 3; if (c) y = add(y, smul(c, U[j])); }
        int mw = 99; for (int k = 0; k < 1024; k++) { int w = wt(add(y, cw[k])); if (w < mw) mw = w; } m16v[t] = mw; if (t) hist16[mw]++; }
    /* V8 classes */
    int hist8[10] = {0};
    for (int idx = 0; idx < Q; idx++) { bv u = {0, 0}; int s = 0; for (int i = 1; i <= 6; i++) { int c = (idx >> (2 * (i - 1))) & 3; put(&u, i, c); s ^= c; } put(&u, 7, s);
        v8[idx] = u; if (v8index(u) != idx) { fprintf(stderr, "v8index\n"); return 5; }
        int mw = 99; bv one = { 0xff, 0 }; for (int l = 0; l < 4; l++) { int w = wt(add(u, smul(l, one))); if (w < mw) mw = w; } m8v[idx] = mw; if (idx) hist8[mw]++; }
    fprintf(stderr, "V8 class counts by m8:"); for (int w = 0; w < 10; w++) if (hist8[w]) fprintf(stderr, " %d:%d", w, hist8[w]); fprintf(stderr, "\n");
    fprintf(stderr, "V2 class counts by m16:"); for (int w = 0; w < 20; w++) if (hist16[w]) fprintf(stderr, " %d:%d", w, hist16[w]); fprintf(stderr, "\n");
    /* G orbits on V8 by explicit enumeration of S8 x F4^* */
    static int orb[Q]; for (int i = 0; i < Q; i++) orb[i] = -1;
    static int perm8[40320][8]; int np8 = 0;
    { int c[8] = {0}, a[8]; for (int i = 0; i < 8; i++) a[i] = i; memcpy(perm8[np8++], a, sizeof a);   /* Heap's algorithm */
      int i = 0; while (i < 8) { if (c[i] < i) { if (i % 2 == 0) { int t = a[0]; a[0] = a[i]; a[i] = t; } else { int t = a[c[i]]; a[c[i]] = a[i]; a[i] = t; }
          memcpy(perm8[np8++], a, sizeof a); c[i]++; i = 0; } else { c[i] = 0; i++; } } }
    if (np8 != 40320) { fprintf(stderr, "perms %d\n", np8); return 6; }
    long long N = 0; int norbits = 0;
    static int members[Q];
    for (int y = 1; y < Q; y++) {
        if (orb[y] >= 0) continue;
        int nm = 0; orb[y] = y; members[nm++] = y;
        for (int p = 0; p < 40320; p++) for (int lam = 1; lam <= 3; lam++) {
            bv w = {0, 0}; for (int i = 0; i < 8; i++) { int c = get(v8[y], i); if (c) put(&w, perm8[p][i], MUL[lam][c]); }
            int z = v8index(w); if (orb[z] < 0) { orb[z] = y; members[nm++] = z; } else if (orb[z] != y) { fprintf(stderr, "orbit clash\n"); return 6; }
        }
        norbits++;
        /* x_0 = y valid? */
        if (herm(v8[y], v8[y], 8) != H[0][0]) continue;
        int ok = 1; for (int a = 1; a <= 3; a++) { int ya = 0; for (int i = 0; i < 6; i++) ya |= MUL[a][(y >> (2 * i)) & 3] << (2 * i); if (m8v[ya] + m16v[a] < 8) ok = 0; }
        if (!ok) continue;
        x[0] = y; s_of[1][0] = 0;
        for (int a = 1; a <= 3; a++) { int ya = 0; for (int i = 0; i < 6; i++) ya |= MUL[a][(y >> (2 * i)) & 3] << (2 * i); s_of[1][a] = ya; }
        /* candidate lists for levels 1..5: norm condition only (products checked in dfs) */
        for (int j = 1; j < 6; j++) { if (!cand[j]) cand[j] = malloc(sizeof(int) * Q); ncand[j] = 0; for (int z = 1; z < Q; z++) if (herm(v8[z], v8[z], 8) == H[j][j] && herm(v8[y], v8[z], 8) == H[0][j]) cand[j][ncand[j]++] = z; }
        ncomp = 0; dfs(1);
        fprintf(stderr, "orbit rep %d size %d m8 %d: completions %lld\n", y, nm, m8v[y], ncomp);
        N += (long long)nm * ncomp;
    }
    printf("line %ld N_phi %lld (orbits %d)\n", want, N, norbits);
    return 0;
}
