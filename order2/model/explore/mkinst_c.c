// Fast instance builder (equivalent to src/mkinst.py up to the choice of basis of each Y_y): same Gram-row
// parametrisation (diagonal equations, gauge pivots at lowest entries, reverse RREF), constraints for low words
// of weight j < 16 with (16-j)/2 >= 1 + (j/2 mod 2); bad syndromes = patterns of size < (16-j)/2 outside y.
// Usage: mkinst_c GENFILE FLAGFILE OUT      (GENFILE: 18 decimal rows; FLAGFILE: line 'FLAG w0 .. w17')
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
#define K 18
#define M 36
#define NE 171
#define NWORDS (1 << K)
typedef struct { u64 w[3]; } m192;               // masks over 171 entries
static inline void mx(m192 *a, const m192 *b) { a->w[0] ^= b->w[0]; a->w[1] ^= b->w[1]; a->w[2] ^= b->w[2]; }
static inline int mb(const m192 *a, int i) { return (a->w[i >> 6] >> (i & 63)) & 1; }
static inline void ms(m192 *a, int i) { a->w[i >> 6] |= 1ULL << (i & 63); }
static inline int mz(const m192 *a) { return !(a->w[0] | a->w[1] | a->w[2]); }
static inline int mlow(const m192 *a) { for (int q = 0; q < 3; q++) if (a->w[q]) return q * 64 + __builtin_ctzll(a->w[q]); return -1; }
static inline int mhigh(const m192 *a) { for (int q = 2; q >= 0; q--) if (a->w[q]) return q * 64 + 63 - __builtin_clzll(a->w[q]); return -1; }
static int EI[K][K];
static u64 G[K], W[K];
static u64 word[NWORDS];
static int popc(u64 x) { return __builtin_popcountll(x); }
// coordinates of x in basis W (by elimination with tracking)
static u64 piv_v[K], piv_t[K]; static int piv_b[K], npiv = 0;
static void coords_init(void) {
    for (int k = 0; k < K; k++) {
        u64 v = W[k], t = 1ULL << k;
        for (int q = 0; q < npiv; q++) if ((v >> piv_b[q]) & 1) { v ^= piv_v[q]; t ^= piv_t[q]; }
        if (!v) { fprintf(stderr, "flag not a basis\n"); exit(1); }
        int b = 63 - __builtin_clzll(v);
        for (int q = 0; q < npiv; q++) if ((piv_v[q] >> b) & 1) { piv_v[q] ^= v; piv_t[q] ^= t; }
        piv_v[npiv] = v; piv_t[npiv] = t; piv_b[npiv] = b; npiv++;
    }
}
static u64 coords(u64 x) {
    u64 t = 0;
    for (int q = 0; q < npiv; q++) if ((x >> piv_b[q]) & 1) { x ^= piv_v[q]; t ^= piv_t[q]; }
    if (x) { fprintf(stderr, "not in span\n"); exit(1); }
    return t;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); for (int k = 0; k < K; k++) { unsigned long long x; if (fscanf(f, "%llu", &x) != 1) return 1; G[k] = x; } fclose(f);
    f = fopen(argv[2], "r"); char tag[16]; if (fscanf(f, "%15s", tag) != 1) return 1;
    for (int k = 0; k < K; k++) { unsigned long long x; if (fscanf(f, "%llu", &x) != 1) return 1; W[k] = x; } fclose(f);
    word[0] = 0; for (int k = 0; k < K; k++) for (int j = 0; j < (1 << k); j++) word[(1 << k) + j] = word[j] ^ G[k];
    coords_init();
    int e = 0; for (int i = 0; i < K; i++) for (int j = i; j < K; j++) { EI[i][j] = EI[j][i] = e++; }
    // equations: masks over entries + rhs
    m192 eqm[400]; int eqr[400], neq = 0;
    u64 ALL = (1ULL << M) - 1, cone = coords(ALL);
    for (int k = 0; k < K; k++) {
        m192 mm = {{0, 0, 0}}; ms(&mm, EI[k][k]);
        for (int j = 0; j < K; j++) if ((cone >> j) & 1) { m192 t = {{0, 0, 0}}; ms(&t, EI[k][j]); mx(&mm, &t); }
        if (!mz(&mm)) { eqm[neq] = mm; eqr[neq] = (popc(W[k]) / 2) & 1; neq++; }
    }
    // gauge pivots (lowest bit), elimination as in mkinst.py
    m192 gpv[40]; int gpb[40], ngp = 0;
    for (int p = 0; p < M; p++) {
        m192 g = {{0, 0, 0}};
        for (int i = 0; i < K; i++) for (int j = i; j < K; j++) if (((W[i] & W[j]) >> p) & 1) ms(&g, EI[i][j]);
        // reduce by existing pivots in ascending pivot order
        int order[40]; for (int q = 0; q < ngp; q++) order[q] = q;
        for (int a = 0; a < ngp; a++) for (int b = a + 1; b < ngp; b++) if (gpb[order[b]] < gpb[order[a]]) { int t = order[a]; order[a] = order[b]; order[b] = t; }
        for (int a = 0; a < ngp; a++) { int q = order[a]; if (mb(&g, gpb[q])) mx(&g, &gpv[q]); }
        if (!mz(&g)) {
            int b = mlow(&g);
            for (int q = 0; q < ngp; q++) if (mb(&gpv[q], b)) mx(&gpv[q], &g);
            gpv[ngp] = g; gpb[ngp] = b; ngp++;
        }
    }
    for (int q = 0; q < ngp; q++) { m192 t = {{0, 0, 0}}; ms(&t, gpb[q]); eqm[neq] = t; eqr[neq] = 0; neq++; }
    // reverse RREF (pivot = highest bit)
    m192 pvm[NE]; int pvr[NE], haspv[NE]; memset(haspv, 0, sizeof haspv);
    int pvlist[NE], npv = 0;
    for (int qe = 0; qe < neq; qe++) {
        m192 mm = eqm[qe]; int r = eqr[qe];
        // reduce by existing pivots in descending order
        for (int b = NE - 1; b >= 0; b--) if (haspv[b] && mb(&mm, b)) { mx(&mm, &pvm[b]); r ^= pvr[b]; }
        if (mz(&mm)) { if (r) { fprintf(stderr, "inconsistent\n"); return 1; } continue; }
        int b = mhigh(&mm);
        for (int q = 0; q < npv; q++) { int b2 = pvlist[q]; if (mb(&pvm[b2], b)) { mx(&pvm[b2], &mm); pvr[b2] ^= r; } }
        pvm[b] = mm; pvr[b] = r; haspv[b] = 1; pvlist[npv++] = b;
    }
    int vidx[NE], N = 0, level[NE];
    for (int x = 0; x < NE; x++) { if (!haspv[x]) { vidx[x] = N; int row = 0; while (EI[row][K - 1] < x) row++; level[N] = row; N++; } else vidx[x] = -1; }
    if (N > 128) { fprintf(stderr, "N>128\n"); return 1; }
    u128 entv[NE]; int entc[NE];
    for (int x = 0; x < NE; x++) {
        if (vidx[x] >= 0) { entv[x] = ((u128)1) << vidx[x]; entc[x] = 0; continue; }
        u128 vm = 0;
        for (int b = 0; b < NE; b++) if (b != x && mb(&pvm[x], b)) { if (vidx[b] < 0 || b > x) { fprintf(stderr, "bad pivot structure\n"); return 1; } vm |= ((u128)1) << vidx[b]; }
        entv[x] = vm; entc[x] = pvr[x];
    }
    int kt[K] = {0}; for (int v = 0; v < N; v++) kt[level[v]]++;
    // constraints
    typedef struct { int lv, wt, m, nb; u128 fm[16]; int fc[16]; int *bad; u64 y; u64 ub[16]; } Cons;
    int cap = 16384, nc = 0; Cons *cs = malloc(sizeof(Cons) * cap);
    for (int j = 1; j < 16; j++) {
        if (!((16 - j) / 2 >= 1 + ((j / 2) % 2))) continue;
        for (u64 uidx = 0; uidx < NWORDS; uidx++) {
            u64 y = word[uidx]; if (popc(y) != j) continue;
            int r = (16 - j) / 2;
            // basis of Y_y = {u : u & y == 0}: kernel of the projection onto supp y, by elimination on coefficient vectors
            // rows: generator coefficient e_k with image G[k] & y; find kernel vectors
            u64 img[K], co[K]; for (int k = 0; k < K; k++) { img[k] = G[k] & y; co[k] = 1ULL << k; }
            int rk = 0;
            for (int bit = 0; bit < M && rk < K; bit++) {
                if (!((y >> bit) & 1)) continue;
                int p = -1; for (int q = rk; q < K; q++) if ((img[q] >> bit) & 1) { p = q; break; }
                if (p < 0) continue;
                u64 t = img[p]; img[p] = img[rk]; img[rk] = t; t = co[p]; co[p] = co[rk]; co[rk] = t;
                for (int q = 0; q < K; q++) if (q != rk && ((img[q] >> bit) & 1)) { img[q] ^= img[rk]; co[q] ^= co[rk]; }
                rk++;
            }
            int mdim = K - rk; if (mdim > 16) { fprintf(stderr, "m>16\n"); return 1; }
            if (nc >= cap) { cap *= 2; cs = realloc(cs, sizeof(Cons) * cap); }
            Cons *C = &cs[nc];
            C->wt = j; C->m = mdim; C->y = y;
            for (int t = 0; t < mdim; t++) { u64 c = co[rk + t]; u64 u = 0; for (int k = 0; k < K; k++) if ((c >> k) & 1) u ^= G[k]; C->ub[t] = u; }
            // bad syndromes: patterns of size < r outside y
            int cols[M]; for (int i = 0; i < M; i++) { int c = 0; for (int t = 0; t < mdim; t++) c |= ((C->ub[t] >> i) & 1) << t; cols[i] = c; }
            static char seen[1 << 16]; memset(seen, 0, 1 << mdim);
            int outp[M], no = 0; for (int i = 0; i < M; i++) if (!((y >> i) & 1)) outp[no++] = i;
            seen[0] = 1;
            if (r > 1) for (int a = 0; a < no; a++) seen[cols[outp[a]]] = 1;
            if (r > 2) for (int a = 0; a < no; a++) for (int b = a + 1; b < no; b++) seen[cols[outp[a]] ^ cols[outp[b]]] = 1;
            if (r > 3) for (int a = 0; a < no; a++) for (int b = a + 1; b < no; b++) for (int c = b + 1; c < no; c++) seen[cols[outp[a]] ^ cols[outp[b]] ^ cols[outp[c]]] = 1;
            int nb = 0; for (int s = 0; s < (1 << mdim); s++) nb += seen[s];
            C->bad = malloc(sizeof(int) * (nb + 1)); C->nb = nb; nb = 0;
            for (int s = 0; s < (1 << mdim); s++) if (seen[s]) C->bad[nb++] = s;
            // forms: B(y, u_t) = sum_{i,j} cy_i cu_j B(w_i, w_j)
            u64 cy = coords(y); int lv = 0;
            for (int t = 0; t < mdim; t++) {
                u64 cu = coords(C->ub[t]); u128 vm = 0; int cc = 0;
                for (int i = 0; i < K; i++) if ((cy >> i) & 1) for (int jj = 0; jj < K; jj++) if ((cu >> jj) & 1) { vm ^= entv[EI[i][jj]]; cc ^= entc[EI[i][jj]]; }
                C->fm[t] = vm; C->fc[t] = cc;
                for (int v = 0; v < N; v++) if (((vm >> v) & 1) && level[v] > lv) lv = level[v];
            }
            C->lv = lv; nc++;
        }
    }
    // stable sort by level
    int *ord = malloc(sizeof(int) * nc); int pos = 0;
    for (int t = 0; t < K; t++) for (int c = 0; c < nc; c++) if (cs[c].lv == t) ord[pos++] = c;
    char fn[4096]; snprintf(fn, sizeof fn, "%s", argv[3]);
    FILE *o = fopen(fn, "w"); snprintf(fn, sizeof fn, "%s.meta", argv[3]); FILE *om = fopen(fn, "w");
    fprintf(o, "%d %d %d\n", N, K, nc);
    int vs = 0; fprintf(o, "0"); for (int t = 0; t < K; t++) { vs += kt[t]; fprintf(o, " %d", vs); } fprintf(o, "\n");
    for (int q = 0; q < nc; q++) {
        Cons *C = &cs[ord[q]];
        fprintf(o, "%d %d %d %d\n", C->lv, C->wt, C->m, C->nb);
        for (int t = 0; t < C->m; t++) {
            u128 v = C->fm[t]; u64 hi = (u64)(v >> 64), lo = (u64)v;
            if (hi) fprintf(o, "%llx%016llx %d\n", (unsigned long long)hi, (unsigned long long)lo, C->fc[t]);
            else fprintf(o, "%llx %d\n", (unsigned long long)lo, C->fc[t]);
        }
        for (int b = 0; b < C->nb; b++) fprintf(o, b ? " %d" : "%d", C->bad[b]); fprintf(o, "\n");
        fprintf(om, "%llu", (unsigned long long)C->y); for (int t = 0; t < C->m; t++) fprintf(om, " %llu", (unsigned long long)C->ub[t]); fprintf(om, "\n");
    }
    fclose(o); fclose(om);
    return 0;
}
