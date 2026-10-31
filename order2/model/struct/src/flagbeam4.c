// Beam search for a good basis order (flag) of Y for the level-wise Gram-row search.
// Heuristic: log2 nodes after level t = F_{t+1} - L_{t+1}; F = sum of free vars per row (18-t-diag-gauge pivots),
// L = sum over low-weight words in W_{t+1} of -log2(pass prob).  Score of a partial flag = log2 sum_s 2^{F_s-L_s}.
// Usage: flagbeam GENFILE LOWFILE BEAM [FIRST36]   GENFILE: 18 decimal rows; LOWFILE: lines "y36 weight"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
#define K 18
#define NW (1 << K)
static u64 G[K]; static u64 word[NW]; static float wl[NW]; static int ci_[36]; // ci_[i] = column i of G (18 bits)
static u64 ALL = (1ULL << 36) - 1;
typedef struct { int t; int b[K]; int ech[K]; int piv[K]; double F, L, score, peak; int kt[K]; int rank; int has1; } State;
static int reduce_(const State *s, int x) { for (int k = 0; k < s->t; k++) if ((x >> s->piv[k]) & 1) x ^= s->ech[k]; return x; }
static void add_vec(State *s, int x) {
    int r = reduce_(s, x); int p = 31 - __builtin_clz(r);
    for (int k = 0; k < s->t; k++) if ((s->ech[k] >> p) & 1) s->ech[k] ^= r;
    s->ech[s->t] = r; s->piv[s->t] = p; s->b[s->t] = x; s->t++;
}
// gauge rank for rows 0..t-1 (basis b[0..t-1]): rank of { u_i (x) c_i } over i, vectors of t*18 bits
static int gauge_rank(const int *b, int t) {
    u64 V[36][6]; int nv = 0;
    for (int i = 0; i < 36; i++) {
        u64 v[6] = {0};
        for (int a = 0; a < t; a++) if ((word[b[a]] >> i) & 1) {
            int off = a * 18; u64 c = (u64)ci_[i];
            v[off / 64] |= c << (off % 64);
            if (off % 64 > 64 - 18) v[off / 64 + 1] |= c >> (64 - off % 64);
        }
        memcpy(V[nv++], v, sizeof v);
    }
    int rank = 0, nwords = (t * 18 + 63) / 64;
    for (int col = 0; col < t * 18 && rank < nv; col++) {
        int w = col / 64, bit = col % 64, p = -1;
        for (int r = rank; r < nv; r++) if ((V[r][w] >> bit) & 1) { p = r; break; }
        if (p < 0) continue;
        if (p != rank) for (int q = 0; q < 6; q++) { u64 tmp = V[p][q]; V[p][q] = V[rank][q]; V[rank][q] = tmp; }
        for (int r = 0; r < nv; r++) if (r != rank && ((V[r][w] >> bit) & 1)) for (int q = 0; q < nwords; q++) V[r][q] ^= V[rank][q];
        rank++;
    }
    return rank;
}
static int cmpstate(const void *a, const void *b) { double x = ((State *)a)->score, y = ((State *)b)->score; return (x > y) - (x < y); }
static double lse2(double a, double b) { double m = a > b ? a : b; return m + log2(exp2(a - m) + exp2(b - m)); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); for (int k = 0; k < K; k++) { unsigned long long x; if (fscanf(f, "%llu", &x) != 1) return 1; G[k] = x; } fclose(f);
    word[0] = 0; for (int k = 0; k < K; k++) for (int j = 0; j < (1 << k); j++) word[(1 << k) + j] = word[j] ^ G[k];
    for (int i = 0; i < 36; i++) { int c = 0; for (int k = 0; k < K; k++) if ((G[k] >> i) & 1) c |= 1 << k; ci_[i] = c; }
    // map 36-bit word -> coefficient index via open addressing
    int HS = 1 << 20; int *ht = malloc(sizeof(int) * HS); memset(ht, -1, sizeof(int) * HS);
    for (int u = 0; u < NW; u++) { u64 h = (word[u] * 0x9E3779B97F4A7C15ULL) >> 44; while (ht[h] >= 0) h = (h + 1) & (HS - 1); ht[h] = u; }
    f = fopen(argv[2], "r"); unsigned long long y; double wt; int nlow = 0; int *lows = malloc(sizeof(int) * NW);
    while (fscanf(f, "%llu %lf", &y, &wt) == 2) {
        u64 h = ((u64)y * 0x9E3779B97F4A7C15ULL) >> 44; while (ht[h] >= 0 && word[ht[h]] != y) h = (h + 1) & (HS - 1);
        if (ht[h] < 0) { fprintf(stderr, "word not in code\n"); return 1; }
        wl[ht[h]] = (float)wt; lows[nlow++] = ht[h];
    }
    fclose(f);
    int BEAM = atoi(argv[3]); int u1 = -1;
    { u64 h = (ALL * 0x9E3779B97F4A7C15ULL) >> 44; while (ht[h] >= 0 && word[ht[h]] != ALL) h = (h + 1) & (HS - 1); u1 = ht[h]; }
    State *beam = calloc(BEAM, sizeof(State)), *nb = calloc((size_t)BEAM * 64, sizeof(State)); int nbeam = 1;
    memset(&beam[0], 0, sizeof(State)); beam[0].score = -1e9;
    if (argc > 4) { // forced first vector(s): decimal 36-bit words separated by commas
        char *tok = strtok(argv[4], ",");
        while (tok) { u64 v = strtoull(tok, NULL, 10); u64 h = (v * 0x9E3779B97F4A7C15ULL) >> 44; while (ht[h] >= 0 && word[ht[h]] != v) h = (h + 1) & (HS - 1);
            int u = ht[h]; State *s = &beam[0]; int t = s->t; double gain = 0;
            for (int m = 0; m < (1 << t); m++) { int x = u; for (int k = 0; k < t; k++) if ((m >> k) & 1) x ^= s->b[k]; gain += wl[x]; }
            int has1 = s->has1 || (reduce_(s, u1) != 0 && reduce_(s, u1) == reduce_(s, u));
            add_vec(s, u); int r = gauge_rank(s->b, s->t); int diag = 1; if (!s->has1 && reduce_(s, u1) == 0) { diag = 0; s->has1 = 1; }
            int kt = 18 - t - diag - (r - s->rank); s->rank = r; s->kt[t] = kt; s->F += kt; s->L += gain;
            s->score = (s->score < -1e8) ? (s->F - s->L) : lse2(s->score, s->F - s->L); if (s->F - s->L > s->peak) s->peak = s->F - s->L;
            (void)has1; tok = strtok(NULL, ","); }
    }
    float *bin = calloc(NW, sizeof(float));
    int *touched = malloc(sizeof(int) * NW);
    int MAXT = getenv("MAXT") ? atoi(getenv("MAXT")) : K;
    while (beam[0].t < MAXT && nbeam > 0) {
        int nn = 0;
        for (int sidx = 0; sidx < nbeam; sidx++) {
            State *s = &beam[sidx]; int t = s->t;
            // accumulate gains per coset (canonical rep = reduce)
            int nt = 0;
            for (int q = 0; q < nlow; q++) { int x = lows[q]; int r = reduce_(s, x); if (!r) continue; if (bin[r] == 0) touched[nt++] = r; bin[r] += wl[x]; }
            // also the all-ones coset as a candidate
            int r1 = reduce_(s, u1); if (r1 && bin[r1] == 0) { touched[nt++] = r1; bin[r1] = 1e-9f; }
            // pick top-C cosets by gain
            int C = 48; int top[64]; float topg[64]; int ntop = 0;
            for (int q = 0; q < nt; q++) { int r = touched[q]; float g = bin[r];
                if (ntop < C) { top[ntop] = r; topg[ntop] = g; ntop++; }
                else { int mi = 0; for (int z = 1; z < ntop; z++) if (topg[z] < topg[mi]) mi = z; if (g > topg[mi]) { top[mi] = r; topg[mi] = g; } } }
            if (r1 && ntop < 64) { int found = 0; for (int z = 0; z < ntop; z++) if (top[z] == r1) found = 1; if (!found) { top[ntop] = r1; topg[ntop] = bin[r1]; ntop++; } }
            for (int z = 0; z < ntop; z++) {
                State ns = *s; int u = top[z]; double gain = topg[z] < 1e-6 ? 0 : topg[z];
                int diag = 1; add_vec(&ns, u); if (!ns.has1 && reduce_(&ns, u1) == 0) { diag = 0; ns.has1 = 1; }
                int r = gauge_rank(ns.b, ns.t); int kt = 18 - t - diag - (r - ns.rank); if (kt < 0) kt = 0;
                ns.rank = r; ns.kt[t] = kt; ns.F += kt; ns.L += gain;
                double ln = ns.F - ns.L; ns.score = (getenv("MAXL") ? -ns.L : ((s->t == 0) ? ln : lse2(s->score, ln))); if (ln > ns.peak || t == 0) ns.peak = (t == 0 ? ln : (ln > s->peak ? ln : s->peak));
                nb[nn++] = ns;
            }
            for (int q = 0; q < nt; q++) bin[touched[q]] = 0;
        }
        qsort(nb, nn, sizeof(State), cmpstate);
        // dedup identical subspaces (same echelon basis)
        int nk = 0;
        for (int q = 0; q < nn && nk < BEAM; q++) {
            int dup = 0;
            for (int z = 0; z < nk && !dup; z++) {
                if (beam[z].t != nb[q].t) continue;
                int same = 1; for (int k = 0; k < nb[q].t && same; k++) if (reduce_(&beam[z], nb[q].b[k])) same = 0;
                if (same && fabs(beam[z].score - nb[q].score) < 1e-9) dup = 1;
            }
            if (!dup) beam[nk++] = nb[q];
        }
        if (nk == 0) break;   // no candidates left (restricted low file exhausted): keep previous beam
        nbeam = nk;
        fprintf(stderr, "t=%d best score %.2f peak %.2f (F=%.0f L=%.1f)\n", beam[0].t, beam[0].score, beam[0].peak, beam[0].F, beam[0].L);
    }
    State *s = &beam[0];
    printf("SCORE %.3f PEAK %.3f\nKT", s->score, s->peak); for (int k = 0; k < s->t; k++) printf(" %d", s->kt[k]); printf("\nFLAG");
    for (int k = 0; k < s->t; k++) printf(" %llu", (unsigned long long)word[s->b[k]]); printf("\n");
    return 0;
}
