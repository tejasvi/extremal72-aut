/* Independent check of E_B level lists (auditor code, rev_reclass).
   For each code D (k rows, hex "%08x%08x" lo/hi planes per row, as in ebcls2 output) of length NB:
   - verify rank k, Hermitian self-orthogonal, d(D) >= DMIN (full enumeration);
   - compute D^perp from scratch (null space of the conjugated generator matrix), a complement of D in D^perp,
     and count the cosets v + D (v in D^perp \ D) with even weight and min weight >= DMIN.
   Output per line: "aut sc nvalid_cosets fullsupp" (aut, sc copied from the input line).
   Element encoding: code c = lo + 2*hi means lo + hi*w, w^2 = w + 1.
   usage: ebmass NB K DMIN FILE [PART NPARTS] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32;
static int MUL[4][4], INV[4], CONJ[4];
static void init_field(void) {
    /* elements as pairs (a,b) = a + b w; product with w^2 = w + 1 */
    for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) {
        int a = x & 1, b = x >> 1, c = y & 1, d = y >> 1;
        int r0 = (a & c) ^ (b & d), r1 = (a & d) ^ (b & c) ^ (b & d);
        MUL[x][y] = r0 | (r1 << 1);
    }
    for (int x = 1; x < 4; x++) for (int y = 1; y < 4; y++) if (MUL[x][y] == 1) INV[x] = y;
    for (int x = 0; x < 4; x++) CONJ[x] = MUL[x][x];   /* Frobenius x -> x^2 */
}
typedef struct { u32 lo, hi; } bv;
static int NB;
static inline int get(bv v, int i) { return ((v.lo >> i) & 1) | (((v.hi >> i) & 1) << 1); }
static inline void put(bv *v, int i, int c) { v->lo = (v->lo & ~(1u << i)) | ((u32)(c & 1) << i); v->hi = (v->hi & ~(1u << i)) | ((u32)(c >> 1) << i); }
static inline bv add(bv a, bv b) { bv r = { a.lo ^ b.lo, a.hi ^ b.hi }; return r; }
static bv smul(int c, bv a) { bv r = {0, 0}; for (int i = 0; i < NB; i++) { int x = get(a, i); if (x) put(&r, i, MUL[c][x]); } return r; }
static inline int wt(bv a) { return __builtin_popcount(a.lo | a.hi); }
static int herm(bv a, bv b) { int s = 0; for (int i = 0; i < NB; i++) s ^= MUL[get(a, i)][CONJ[get(b, i)]]; return s; }
/* rank by elimination on copies */
static int rank_of(const bv *g, int k) {
    bv m[40]; memcpy(m, g, sizeof(bv) * k); int r = 0;
    for (int col = 0; col < NB && r < k; col++) {
        int s = -1; for (int i = r; i < k; i++) if (get(m[i], col)) { s = i; break; }
        if (s < 0) continue;
        bv t = m[s]; m[s] = m[r]; m[r] = t; m[r] = smul(INV[get(m[r], col)], m[r]);
        for (int i = 0; i < k; i++) if (i != r) { int c = get(m[i], col); if (c) m[i] = add(m[i], smul(c, m[r])); }
        r++;
    }
    return r;
}
int main(int argc, char **argv) {
    init_field();
    NB = atoi(argv[1]); int K = atoi(argv[2]), DMIN = atoi(argv[3]);
    int part = argc > 6 ? atoi(argv[5]) : 0, nparts = argc > 6 ? atoi(argv[6]) : 1;
    FILE *f = fopen(argv[4], "r"); char line[8192]; long li = -1;
    while (fgets(line, sizeof line, f)) {
        li++; if (li % nparts != part) continue;
        bv D[16]; char *q = line;
        for (int r = 0; r < K; r++) { char h[9]; memcpy(h, q, 8); h[8] = 0; D[r].lo = strtoul(h, 0, 16); memcpy(h, q + 8, 8); h[8] = 0; D[r].hi = strtoul(h, 0, 16); q += 16; }
        long aut; int sc; if (sscanf(q, "%ld %d", &aut, &sc) != 2) { fprintf(stderr, "parse\n"); return 2; }
        if (rank_of(D, K) != K) { fprintf(stderr, "line %ld rank\n", li); return 3; }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (herm(D[i], D[j])) { fprintf(stderr, "line %ld not s.o.\n", li); return 3; }
        /* all codewords of D */
        long nd = 1L << (2 * K); bv *cw = malloc(sizeof(bv) * nd);
        for (long t = 0; t < nd; t++) { bv x = {0, 0}; for (int j = 0; j < K; j++) { int c = (t >> (2 * j)) & 3; if (c) x = add(x, smul(c, D[j])); } cw[t] = x; }
        u32 sup = 0; for (long t = 1; t < nd; t++) { if (wt(cw[t]) < DMIN) { fprintf(stderr, "line %ld weight %d\n", li, wt(cw[t])); return 3; } sup |= cw[t].lo | cw[t].hi; }
        int fs = sup == (NB == 32 ? 0xffffffffu : ((1u << NB) - 1));
        /* D^perp: solve sum_i conj(D_r[i]) x_i = 0. Matrix A rows a_r = conj(D_r). RREF of A. */
        bv A[16]; for (int r = 0; r < K; r++) { bv x = {0, 0}; for (int i = 0; i < NB; i++) put(&x, i, CONJ[get(D[r], i)]); A[r] = x; }
        int piv[16], rr = 0;
        for (int col = 0; col < NB && rr < K; col++) {
            int s = -1; for (int i = rr; i < K; i++) if (get(A[i], col)) { s = i; break; }
            if (s < 0) continue;
            bv t = A[s]; A[s] = A[rr]; A[rr] = t; A[rr] = smul(INV[get(A[rr], col)], A[rr]);
            for (int i = 0; i < K; i++) if (i != rr) { int c = get(A[i], col); if (c) A[i] = add(A[i], smul(c, A[rr])); }
            piv[rr++] = col;
        }
        int ispiv[32] = {0}; for (int i = 0; i < rr; i++) ispiv[piv[i]] = 1;
        bv P[32]; int np = 0;
        for (int j = 0; j < NB; j++) if (!ispiv[j]) {   /* free variable x_j = 1, pivots x_{piv[i]} = -A[i][j] = A[i][j] */
            bv x = {0, 0}; put(&x, j, 1); for (int i = 0; i < rr; i++) put(&x, piv[i], get(A[i], j)); P[np++] = x; }
        for (int t = 0; t < np; t++) for (int r = 0; r < K; r++) if (herm(P[t], D[r])) { fprintf(stderr, "perp bug\n"); return 4; }
        /* complement of D in D^perp */
        bv cur[40]; int nc = 0; for (int r = 0; r < K; r++) cur[nc++] = D[r];
        bv Wc[32]; int nw = 0;
        for (int t = 0; t < np; t++) { cur[nc] = P[t]; if (rank_of(cur, nc + 1) == nc + 1) { nc++; Wc[nw++] = P[t]; } }
        if (nc != NB - K || nw != NB - 2 * K) { fprintf(stderr, "dims %d %d\n", nc, nw); return 4; }
        /* enumerate cosets by Gray code over F2-basis {Wc_j, w*Wc_j} */
        bv B2[64]; int m2 = 0; for (int j = 0; j < nw; j++) { B2[m2++] = Wc[j]; B2[m2++] = smul(2, Wc[j]); }
        bv v = {0, 0}; long nvalid = 0;
        for (uint64_t g = 1; g < (1ULL << m2); g++) {
            v = add(v, B2[__builtin_ctzll(g)]);
            if (wt(v) & 1) continue;
            int ok = 1; for (long t = 0; t < nd; t++) { bv y = { v.lo ^ cw[t].lo, v.hi ^ cw[t].hi }; if (__builtin_popcount(y.lo | y.hi) < DMIN) { ok = 0; break; } }
            nvalid += ok;
        }
        printf("%ld %d %ld %d\n", aut, sc, nvalid, fs);
        fflush(stdout);
        free(cw);
    }
    return 0;
}
