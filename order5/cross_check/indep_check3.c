// Faster, OpenMP version of indep_check.c (same independent primitives; combos ordered by M_A).
// Reads all node lines, checks them in parallel, prints disagreements/bad nodes and per-k totals.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
static int T = 16;
static const int ORDX[7] = {0,1,3,2,4,5,6};
static const int LN[7][3] = {{0,1,3},{1,2,4},{2,3,5},{3,4,6},{4,5,0},{5,6,1},{6,0,2}};
static int MU[16][16], IV[16], CJ[16], NM[16], WD[16], CL[16], RP[4];
static uint8_t Mw[2187];
static int P3[8];
static int GLp[200][7], nG = 0;
static uint16_t KEYT[1 << 14];
static uint16_t B3a[256], B3b[256], B3c[256], B3d[16];
static uint8_t SMB2[16][256];

static int fmul(int a, int b) { int r = 0; while (b) { if (b & 1) r ^= a; b >>= 1; a <<= 1; if (a & 16) a ^= 0x1F; } return r; }
static int fpow(int a, int e) { int r = 1; while (e--) r = fmul(r, a); return r; }
static void perm_rec(int *p, int k, int *used) {
    if (k == 7) {
        for (int l = 0; l < 7; l++) {
            int m = (1 << p[LN[l][0]]) | (1 << p[LN[l][1]]) | (1 << p[LN[l][2]]), f = 0;
            for (int t = 0; t < 7; t++) if (m == ((1 << LN[t][0]) | (1 << LN[t][1]) | (1 << LN[t][2]))) f = 1;
            if (!f) return;
        }
        memcpy(GLp[nG++], p, 7 * sizeof(int));
        return;
    }
    for (int x = 0; x < 7; x++) if (!used[x]) { used[x] = 1; p[k] = x; perm_rec(p, k + 1, used); used[x] = 0; }
}
static void setup(void) {
    for (int a = 0; a < 16; a++) for (int b = 0; b < 16; b++) MU[a][b] = fmul(a, b);
    for (int a = 0; a < 16; a++) {
        CJ[a] = fpow(a, 4); NM[a] = fpow(a, 5); IV[a] = 0;
        for (int b = 1; b < 16; b++) if (MU[a][b] == 1) IV[a] = b;
        WD[a] = a == 0 ? 0 : (NM[a] == 1 ? 2 : 1);
    }
    int w = 0; for (int a = 1; a < 16; a++) if (NM[a] != 1) { w = NM[a]; break; }
    for (int a = 0; a < 16; a++) CL[a] = a == 0 ? 0 : (NM[a] == 1 ? 1 : (NM[a] == w ? 2 : 3));
    for (int c = 1; c < 4; c++) for (int a = 15; a >= 1; a--) if (CL[a] == c) RP[c] = a;
    int S[16], X[16], n = 1; S[0] = 0; X[0] = 0;
    for (int l = 0; l < 7; l++) {
        int gs = (1 << LN[l][0]) | (1 << LN[l][1]) | (1 << LN[l][2]), nn = n;
        for (int i = 0; i < n; i++) {
            int s2 = S[i] ^ gs, x2 = X[i] ^ 1, dup = 0;
            for (int j = 0; j < nn; j++) if (S[j] == s2 && X[j] == x2) dup = 1;
            if (!dup) { S[nn] = s2; X[nn] = x2; nn++; }
        }
        n = nn;
    }
    if (n != 16) exit(1);
    P3[0] = 1; for (int i = 1; i < 8; i++) P3[i] = 3 * P3[i - 1];
    for (int idx = 0; idx < 2187; idx++) {
        int wv[7], t = idx; for (int j = 0; j < 7; j++) { wv[j] = 2 * (t % 3); t /= 3; }
        int best = 1 << 30;
        for (int k = 0; k < 16; k++) {
            int h = 5 * __builtin_popcount(S[k]) + X[k];
            for (int j = 0; j < 7; j++) h += ((S[k] >> j) & 1) ? -wv[j] : wv[j];
            if (h < best) best = h;
        }
        Mw[idx] = (uint8_t)best;
    }
    int p[7], used[7] = {0}; perm_rec(p, 0, used);
    if (nG != 168) exit(1);
    for (int q = 0; q < (1 << 14); q++) {
        int best = q;
        for (int g = 0; g < nG; g++) for (int sw = 0; sw < 2; sw++) {
            int r = 0;
            for (int j = 0; j < 7; j++) { int c = (q >> (2 * j)) & 3; if (sw && c >= 2) c = 5 - c; r |= c << (2 * GLp[g][j]); }
            if (r < best) best = r;
        }
        KEYT[q] = (uint16_t)best;
    }
    for (int b = 0; b < 256; b++) {
        B3a[b] = WD[b & 15] * P3[0] + WD[b >> 4] * P3[1];
        B3b[b] = WD[b & 15] * P3[2] + WD[b >> 4] * P3[3];
        B3c[b] = WD[b & 15] * P3[4] + WD[b >> 4] * P3[5];
    }
    for (int a = 0; a < 16; a++) B3d[a] = WD[a] * P3[6];
    for (int s = 0; s < 16; s++) for (int b = 0; b < 256; b++) SMB2[s][b] = MU[s][b & 15] | (MU[s][b >> 4] << 4);
}
static inline int nb(uint32_t v, int j) { return (v >> (4 * j)) & 15; }
static inline int b3(uint32_t v) { return B3a[v & 255] + B3b[(v >> 8) & 255] + B3c[(v >> 16) & 255] + B3d[(v >> 24) & 15]; }
static inline uint32_t sm(int s, uint32_t v) { return SMB2[s][v & 255] | ((uint32_t)SMB2[s][(v >> 8) & 255] << 8) | ((uint32_t)SMB2[s][(v >> 16) & 255] << 16) | ((uint32_t)MU[s][(v >> 24) & 15] << 24); }
static int pat(uint32_t v) { int r = 0; for (int j = 0; j < 7; j++) r |= CL[nb(v, j)] << (2 * j); return r; }
static int hp(uint32_t u, uint32_t v) { int s = 0; for (int j = 0; j < 7; j++) s ^= MU[nb(u, j)][CJ[nb(v, j)]]; return s; }
static int fin(int *par, int x) { while (par[x] != x) x = par[x]; return x; }
static int forest_ok(const uint32_t *rows, int k) {
    int par[14]; for (int i = 0; i < 14; i++) par[i] = i;
    for (int d = 0; d < k; d++) for (int j = 0; j < 7; j++) {
        int e = nb(rows[d], j); if (!e) continue;
        int a = fin(par, d), b = fin(par, 7 + j);
        if (a != b) { if (e != RP[CL[e]]) return 0; par[a] = b; }
    }
    return 1;
}
static int complement(const uint32_t *rows, int k, uint32_t *basis) {
    int A[7][7];
    for (int i = 0; i < k; i++) for (int j = 0; j < 7; j++) A[i][j] = CJ[nb(rows[i], j)];
    int piv[7], np = 0, r = 0;
    for (int c = 0; c < 7 && r < k; c++) {
        int p = -1; for (int i = r; i < k; i++) if (A[i][c]) { p = i; break; }
        if (p < 0) continue;
        for (int j = 0; j < 7; j++) { int t = A[r][j]; A[r][j] = A[p][j]; A[p][j] = t; }
        int iv = IV[A[r][c]]; for (int j = 0; j < 7; j++) A[r][j] = MU[iv][A[r][j]];
        for (int i = 0; i < k; i++) if (i != r && A[i][c]) { int f = A[i][c]; for (int j = 0; j < 7; j++) A[i][j] ^= MU[f][A[r][j]]; }
        piv[np++] = c; r++;
    }
    if (np != k) return -1;
    int nbas = 0;
    for (int fc = 0; fc < 7; fc++) {
        int isp = 0; for (int t = 0; t < np; t++) if (piv[t] == fc) isp = 1;
        if (isp) continue;
        int v[7] = {0}; v[fc] = 1;
        for (int t = 0; t < np; t++) v[piv[t]] = A[t][fc];
        uint32_t pv = 0; for (int j = 0; j < 7; j++) pv |= (uint32_t)v[j] << (4 * j);
        basis[nbas++] = pv;
    }
    return nbas;
}
typedef struct { int k; uint32_t rows[6]; long kids; } Node;
// returns -1 bad node, else canonical child count; *nfree = all valid children (no symmetry rule)
static long check_node(const Node *nd, long *nfree, uint32_t *cb, uint16_t *ca, uint32_t *ord) {
    int k = nd->k; uint32_t rows[7]; memcpy(rows, nd->rows, k * sizeof(uint32_t));
    long n = 1L << (4 * k);
    for (long i = 0; i < n; i++) {
        uint32_t b = 0; int a = 0;
        for (int t = 0; t < k; t++) { int l = (i >> (4 * t)) & 15; if (l) { b ^= sm(l, rows[t]); a += WD[l] * P3[ORDX[t]]; } }
        cb[i] = b; ca[i] = (uint16_t)a;
    }
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (hp(rows[i], rows[j]) != (i == j)) return -1;
    for (long i = 1; i < n; i++) if (Mw[ca[i]] + Mw[b3(cb[i])] < T) return -1;
    int key0 = KEYT[pat(rows[0])];
    if (key0 != pat(rows[0])) return -1;
    for (int i = 0; i < k; i++) if (KEYT[pat(rows[i])] < key0) return -1;
    if (!forest_ok(rows, k)) return -1;
    // all (combo i, coefficient l) pairs, sorted by exact M_A ascending (counting sort on even M <= 16)
    int pos = ORDX[k];
    long q = 0;
    for (int m = 0; m <= 40; m += 2)
        for (long i = 0; i < n; i++) {
            int m2 = Mw[ca[i] + P3[pos]], m4 = Mw[ca[i] + 2 * P3[pos]];
            if (m2 != m && m4 != m) continue;
            for (int l = 1; l < 16; l++) if (Mw[ca[i] + WD[l] * P3[pos]] == m) ord[q++] = (uint32_t)((i << 4) | l);
        }
    if (q != 15 * n) { fprintf(stderr, "ord error\n"); exit(2); }
    uint32_t bas[7]; int nbas = complement(rows, k, bas);
    if (nbas != 7 - k) return -1;
    long ncan = 0, nf = 0, tot = 1L << (4 * nbas);
    for (long c = 1; c < tot; c++) {
        uint32_t v = 0;
        for (int t = 0; t < nbas; t++) { int l = (c >> (4 * t)) & 15; if (l) v ^= sm(l, bas[t]); }
        if (hp(v, v) != 1) continue;
        uint32_t lv[16]; int da[16];
        for (int l = 1; l < 16; l++) { lv[l] = sm(l, v); da[l] = WD[l] * P3[pos]; }
        int ok = 1;
        for (long t = 0; t < q; t++) {
            uint32_t e = ord[t]; long i = e >> 4; int l = e & 15;
            if (Mw[ca[i] + da[l]] + Mw[b3(cb[i] ^ lv[l])] < T) { ok = 0; break; }
        }
        if (!ok) continue;
        nf++;
        rows[k] = v;
        if (KEYT[pat(v)] >= key0 && forest_ok(rows, k + 1)) ncan++;
    }
    *nfree = nf;
    return ncan;
}
int main(void) {
    if (getenv("T")) T = atoi(getenv("T"));
    setup();
    long cap = 1 << 20, nn = 0; Node *nodes = malloc(cap * sizeof(Node));
    char line[512];
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] != 'N') continue;
        if (nn == cap) { cap *= 2; nodes = realloc(nodes, cap * sizeof(Node)); }
        Node *nd = &nodes[nn]; nd->k = line[1] - '0';
        char *s = line + 2; for (int i = 0; i < nd->k; i++) nd->rows[i] = (uint32_t)strtoul(s, &s, 16);
        char *q = strstr(line, "kids="); nd->kids = q ? atol(q + 5) : -1;
        nn++;
    }
    long cntk[8] = {0}, sumkids[8] = {0}, sumcan[8] = {0}, sumfree[8] = {0}, dis = 0, bad = 0;
    #pragma omp parallel
    {
        uint32_t *cb = malloc((1L << 20) * sizeof(uint32_t)); uint16_t *ca = malloc((1L << 20) * sizeof(uint16_t));
        uint32_t *ord = malloc(15L * (1L << 20) * sizeof(uint32_t));
        long lc[8] = {0}, lk[8] = {0}, lcan[8] = {0}, lf[8] = {0}, ld = 0, lb = 0;
        #pragma omp for schedule(dynamic, 64)
        for (long t = 0; t < nn; t++) {
            long nf = 0; long c = check_node(&nodes[t], &nf, cb, ca, ord);
            int k = nodes[t].k;
            if (c < 0) {
                lb++;
                #pragma omp critical
                { printf("BADNODE k=%d", k); for (int i = 0; i < k; i++) printf(" %07x", nodes[t].rows[i]); printf("\n"); }
                continue;
            }
            lc[k]++; lk[k] += nodes[t].kids; lcan[k] += c; lf[k] += nf;
            if (c != nodes[t].kids) {
                ld++;
                #pragma omp critical
                { printf("DISAGREE k=%d search=%ld indep=%ld free=%ld:", k, nodes[t].kids, c, nf); for (int i = 0; i < k; i++) printf(" %07x", nodes[t].rows[i]); printf("\n"); }
            }
        }
        #pragma omp critical
        { for (int k = 0; k < 8; k++) { cntk[k] += lc[k]; sumkids[k] += lk[k]; sumcan[k] += lcan[k]; sumfree[k] += lf[k]; } dis += ld; bad += lb; }
        free(cb); free(ca); free(ord);
    }
    for (int k = 1; k < 8; k++) if (cntk[k])
        printf("k=%d nodes=%ld  sum search kids=%ld  sum indep canon=%ld  sum indep free=%ld\n", k, cntk[k], sumkids[k], sumcan[k], sumfree[k]);
    printf("SUMMARY T=%d nodes=%ld disagree=%ld badnodes=%ld\n", T, nn, dis, bad);
    return (dis || bad) ? 1 : 0;
}
