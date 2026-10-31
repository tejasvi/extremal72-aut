// Independent re-check of dumped search nodes (own field arithmetic, own e8/M, own GL(3,2), own
// canonical-form tests, own orthogonal-complement enumeration).  For a node with k rows (placed at
// A-coordinates ORD[0..k-1]) it
//   (1) re-verifies the node: rows orthonormal, every nonzero codeword supported on those
//       coordinates has M_A + M_B >= T, and the node is in the canonical form;
//   (2) enumerates EVERY vector v of the (7-k)-dimensional orthogonal complement with <v,v> = 1 and
//       counts those for which all codewords with a nonzero coefficient on v pass ("free" count, no
//       symmetry constraint at all), and among them those that also satisfy the canonical-form rules
//       ("canon" count: key(v) >= key(row 0), mu5 spanning-forest normalisation);
//   (3) for 5-row nodes, additionally tries the 6th row at A-coordinate 6 instead of 5.
// Input lines: "N<k> r0 ... r(k-1) kids=<search count> pool=<n>" (rows packed: nibble j = column j).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int T = 16;
static const int ORDX[7] = {0,1,3,2,4,5,6};
static const int LN[7][3] = {{0,1,3},{1,2,4},{2,3,5},{3,4,6},{4,5,0},{5,6,1},{6,0,2}};
static int MU[16][16], IV[16], CJ[16], NM[16], WT[16], WD[16], CL[16], RP[4];
static int Mw[2187];            // M on weight vectors, base-3 digits (0,1,2) <-> weights (0,2,4)
static int P3[8];
static int GLp[200][7], nG = 0;
static uint16_t KEYT[1 << 14];

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
        WT[a] = a == 0 ? 0 : (NM[a] == 1 ? 4 : 2);
        WD[a] = WT[a] / 2;    // base-3 digit
    }
    int w = 0; for (int a = 1; a < 16; a++) if (NM[a] != 1) { w = NM[a]; break; }
    for (int a = 0; a < 16; a++) CL[a] = a == 0 ? 0 : (NM[a] == 1 ? 1 : (NM[a] == w ? 2 : 3));
    for (int c = 1; c < 4; c++) for (int a = 15; a >= 1; a--) if (CL[a] == c) RP[c] = a;   // smallest of class c
    // e8 = F2-span of (line, 1)
    int S[16], X[16], n = 1; S[0] = 0; X[0] = 0;
    for (int l = 0; l < 7; l++) {
        int gs = (1 << LN[l][0]) | (1 << LN[l][1]) | (1 << LN[l][2]);
        int nn = n;
        for (int i = 0; i < n; i++) {
            int s2 = S[i] ^ gs, x2 = X[i] ^ 1, dup = 0;
            for (int j = 0; j < nn; j++) if (S[j] == s2 && X[j] == x2) dup = 1;
            if (!dup) { S[nn] = s2; X[nn] = x2; nn++; }
        }
        n = nn;
    }
    if (n != 16) { fprintf(stderr, "e8 size %d\n", n); exit(1); }
    P3[0] = 1; for (int i = 1; i < 8; i++) P3[i] = 3 * P3[i - 1];
    for (int idx = 0; idx < 2187; idx++) {
        int wv[7], t = idx; for (int j = 0; j < 7; j++) { wv[j] = 2 * (t % 3); t /= 3; }
        int best = 1 << 30;
        for (int k = 0; k < 16; k++) {
            int h = 5 * __builtin_popcount(S[k]) + X[k];
            for (int j = 0; j < 7; j++) h += ((S[k] >> j) & 1) ? -wv[j] : wv[j];
            if (h < best) best = h;
        }
        Mw[idx] = best;
    }
    int p[7], used[7] = {0}; perm_rec(p, 0, used);
    if (nG != 168) { fprintf(stderr, "GL size %d\n", nG); exit(1); }
    for (int q = 0; q < (1 << 14); q++) {
        int best = q;
        for (int g = 0; g < nG; g++) for (int sw = 0; sw < 2; sw++) {
            int r = 0;
            for (int j = 0; j < 7; j++) { int c = (q >> (2 * j)) & 3; if (sw && c >= 2) c = 5 - c; r |= c << (2 * GLp[g][j]); }
            if (r < best) best = r;
        }
        KEYT[q] = (uint16_t)best;
    }
}
static inline int nb(uint32_t v, int j) { return (v >> (4 * j)) & 15; }
static int pat(uint32_t v) { int r = 0; for (int j = 0; j < 7; j++) r |= CL[nb(v, j)] << (2 * j); return r; }
static int b3B(uint32_t v) { int r = 0; for (int j = 0; j < 7; j++) r += WD[nb(v, j)] * P3[j]; return r; }
static uint32_t sm(int s, uint32_t v) { uint32_t r = 0; for (int j = 0; j < 7; j++) r |= (uint32_t)MU[s][nb(v, j)] << (4 * j); return r; }
static int hp(uint32_t u, uint32_t v) { int s = 0; for (int j = 0; j < 7; j++) s ^= MU[nb(u, j)][CJ[nb(v, j)]]; return s; }
// canonical mu5 spanning forest: process rows 0..k-1 then cand (row index k), row-major, columns 0..6
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
// all codewords supported on A-coordinates ORD[0..k-1] (rows[0..k-1]) with a nonzero coefficient on
// row k-1 placed at A-coordinate posk: returns 1 if all pass
static int test_last(const uint32_t *rows, int k, int posk) {
    long n = 1L << (4 * (k - 1));
    for (long i = 0; i < n; i++) {
        uint32_t b = 0; int ai = 0;
        for (int t = 0; t < k - 1; t++) { int l = (i >> (4 * t)) & 15; if (l) { b ^= sm(l, rows[t]); ai += WD[l] * P3[ORDX[t]]; } }
        for (int l = 1; l < 16; l++) {
            uint32_t bb = b ^ sm(l, rows[k - 1]);
            if (Mw[ai + WD[l] * P3[posk]] + Mw[b3B(bb)] < T) return 0;
        }
    }
    return 1;
}
// orthogonal complement of rows[0..k-1] w.r.t. sum u_j conj(v_j): basis of dim 7-k
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
        for (int t = 0; t < np; t++) v[piv[t]] = A[t][fc];   // char 2: -x = x
        uint32_t pv = 0; for (int j = 0; j < 7; j++) pv |= (uint32_t)v[j] << (4 * j);
        basis[nbas++] = pv;
    }
    return nbas;
}
int main(int argc, char **argv) {
    if (getenv("T")) T = atoi(getenv("T"));
    setup();
    char line[512]; long nodes = 0, agree = 0, disagree = 0, badnode = 0, free_nonzero = 0, alt6 = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] != 'N') continue;
        int k = line[1] - '0';
        uint32_t rows[8]; char *s = line + 2;
        for (int i = 0; i < k; i++) rows[i] = (uint32_t)strtoul(s, &s, 16);
        long kids = -1; char *q = strstr(line, "kids="); if (q) kids = atol(q + 5);
        nodes++;
        // (1) node validity
        int ok = 1;
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (hp(rows[i], rows[j]) != (i == j)) ok = 0;
        for (int d = 1; d <= k && ok; d++) if (!test_last(rows, d, ORDX[d - 1])) ok = 0;
        int key0 = KEYT[pat(rows[0])];
        if (key0 != pat(rows[0])) ok = 0;
        for (int i = 0; i < k; i++) if (KEYT[pat(rows[i])] < key0) ok = 0;
        if (!forest_ok(rows, k)) ok = 0;
        if (!ok) { badnode++; printf("BADNODE %s", line); continue; }
        // (2) all extensions at A-coordinate ORD[k]
        uint32_t bas[7]; int nbas = complement(rows, k, bas);
        if (nbas != 7 - k) { printf("RANKERR %s", line); badnode++; continue; }
        long nfree = 0, ncan = 0, nfree6 = 0; long tot = 1L << (4 * nbas);
        for (long c = 1; c < tot; c++) {
            uint32_t v = 0;
            for (int t = 0; t < nbas; t++) { int l = (c >> (4 * t)) & 15; if (l) v ^= sm(l, bas[t]); }
            if (hp(v, v) != 1) continue;
            for (int i = 0; i < k; i++) if (hp(v, rows[i])) { fprintf(stderr, "complement error\n"); exit(1); }
            rows[k] = v;
            if (test_last(rows, k + 1, ORDX[k])) {
                nfree++;
                if (KEYT[pat(v)] >= key0 && forest_ok(rows, k + 1)) ncan++;
            }
            if (k == 5 && test_last(rows, k + 1, 6)) nfree6++;
        }
        if (ncan == kids) agree++; else { disagree++; printf("DISAGREE "); }
        if (nfree) free_nonzero++;
        if (nfree6) alt6++;
        printf("node %ld k=%d search_kids=%ld indep_canon=%ld indep_free=%ld%s", nodes, k, kids, ncan, nfree, k == 5 ? "" : "\n");
        if (k == 5) printf(" free_at_coord6=%ld\n", nfree6);
    }
    printf("SUMMARY T=%d nodes=%ld agree=%ld disagree=%ld badnodes=%ld nodes_with_free_ext=%ld k5_nodes_with_ext_at_6=%ld\n",
           T, nodes, agree, disagree, badnode, free_nonzero, alt6);
    return disagree || badnode;
}
