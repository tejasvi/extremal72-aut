/* Parity-certificate checker.  Verifies g(x) = expected for every x in F2^N of Hamming weight <= D, where
   g(x) = sum_w G_w(s_w(x)) mod 2, s_w(x) = s0[w] ^ XOR_{v in supp x} E[v][w], G_w given by bit tables.
   If deg(g) <= D (as an F2-polynomial in x) this proves g == expected identically (minimal-monomial argument).
   usage: parcheck DATAFILE D part nparts     (subsets whose minimum element = part mod nparts; empty set in part 0)
   Output: counts of points checked and violations (first few violating subsets printed). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N, W, expected, D;
static int nz, nt;                 /* zero-test words (G = [s=0]) and table words */
static uint16_t *s0z, *s0t;        /* base syndromes */
static uint16_t **Ez, **Et;        /* direction syndromes per variable */
static uint64_t **tab;             /* tables for table words */
static uint16_t **bufz, **buft;    /* per-depth syndrome buffers */
static long long npts = 0, nviol = 0;
static int stackv[64];
static int eval(int depth) {
    const uint16_t *sz = bufz[depth], *st = buft[depth];
    int cnt = 0;
    for (int i = 0; i < nz; i++) cnt += (sz[i] == 0);
    int par = cnt & 1;
    for (int i = 0; i < nt; i++) { uint16_t s = st[i]; par ^= (int)((tab[i][s >> 6] >> (s & 63)) & 1); }
    return par;
}
static void visit(int depth) {
    npts++;
    int g = eval(depth);
    if (g != expected) {
        nviol++;
        if (nviol <= 10) { printf("VIOLATION at subset {"); for (int i = 0; i < depth; i++) printf("%d%s", stackv[i], i + 1 < depth ? "," : ""); printf("}\n"); fflush(stdout); }
    }
}
static void rec(int depth, int start) {
    /* depth = current subset size (already visited); extend with v >= start */
    if (depth == D) return;
    for (int v = start; v < N; v++) {
        uint16_t *pz = bufz[depth], *pt = buft[depth], *qz = bufz[depth + 1], *qt = buft[depth + 1];
        const uint16_t *ez = Ez[v], *et = Et[v];
        for (int i = 0; i < nz; i++) qz[i] = pz[i] ^ ez[i];
        for (int i = 0; i < nt; i++) qt[i] = pt[i] ^ et[i];
        stackv[depth] = v;
        visit(depth + 1);
        rec(depth + 1, v + 1);
    }
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: parcheck DATAFILE D part nparts\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    D = atoi(argv[2]); int part = atoi(argv[3]), nparts = atoi(argv[4]);
    if (fscanf(f, "%d %d %d", &N, &W, &expected) != 3) return 1;
    int *r = malloc(W * sizeof(int)); char **ts = malloc(W * sizeof(char *));
    int *iszero = malloc(W * sizeof(int));
    char buf[1 << 12];
    for (int w = 0; w < W; w++) {
        if (fscanf(f, "%d %4000s", &r[w], buf) != 2) return 1;
        ts[w] = strdup(buf);
        iszero[w] = (strcmp(buf, "1") == 0);
    }
    nz = 0; nt = 0;
    for (int w = 0; w < W; w++) { if (iszero[w]) nz++; else nt++; }
    int *idx = malloc(W * sizeof(int)); int az = 0, at = 0;
    for (int w = 0; w < W; w++) idx[w] = iszero[w] ? az++ : at++;
    tab = malloc((nt + 1) * sizeof(uint64_t *));
    for (int w = 0; w < W; w++) if (!iszero[w]) {
        int words = ((1 << r[w]) + 63) / 64; uint64_t *t = calloc(words > 0 ? words : 1, sizeof(uint64_t));
        /* hex string, most significant first */
        int L = strlen(ts[w]);
        for (int c = 0; c < L; c++) {
            char ch = ts[w][L - 1 - c]; int val = (ch <= '9') ? ch - '0' : (ch | 32) - 'a' + 10;
            for (int b = 0; b < 4; b++) if ((val >> b) & 1) { int bit = 4 * c + b; t[bit >> 6] |= 1ULL << (bit & 63); }
        }
        tab[idx[w]] = t;
    }
    s0z = malloc((nz + 1) * 2); s0t = malloc((nt + 1) * 2);
    for (int w = 0; w < W; w++) { int v; if (fscanf(f, "%d", &v) != 1) return 1; if (iszero[w]) s0z[idx[w]] = v; else s0t[idx[w]] = v; }
    Ez = malloc(N * sizeof(uint16_t *)); Et = malloc(N * sizeof(uint16_t *));
    for (int v = 0; v < N; v++) {
        Ez[v] = malloc((nz + 1) * 2); Et[v] = malloc((nt + 1) * 2);
        for (int w = 0; w < W; w++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; if (iszero[w]) Ez[v][idx[w]] = x; else Et[v][idx[w]] = x; }
    }
    fclose(f);
    bufz = malloc((D + 2) * sizeof(uint16_t *)); buft = malloc((D + 2) * sizeof(uint16_t *));
    for (int dd = 0; dd <= D + 1; dd++) { bufz[dd] = malloc((nz + 1) * 2); buft[dd] = malloc((nt + 1) * 2); }
    memcpy(bufz[0], s0z, nz * 2); memcpy(buft[0], s0t, nt * 2);
    if (part == 0) visit(0);
    if (D >= 1) {
        for (int v = part; v < N; v += nparts) {
            for (int i = 0; i < nz; i++) bufz[1][i] = bufz[0][i] ^ Ez[v][i];
            for (int i = 0; i < nt; i++) buft[1][i] = buft[0][i] ^ Et[v][i];
            stackv[0] = v;
            visit(1);
            rec(1, v + 1);
        }
    }
    printf("N %d W %d (zero-test %d, table %d) D %d part %d/%d: points %lld violations %lld\n", N, W, nz, nt, D, part, nparts, npts, nviol);
    return 0;
}
