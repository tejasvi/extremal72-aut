// Naive reference engine for lwe instance files (independent parser and evaluation; no Gray code, no RREF).
// At a node of level t every child v (0 .. 2^k_t - 1) is tested against every constraint of level t by computing
// each syndrome bit directly as parity(form & assignment) ^ const and looking it up in a byte table of bad syndromes.
// Usage: naive INSTANCE count            -> LEVEL / SOLUTION / DONE lines (same counting convention as lwe)
//        naive INSTANCE probe L SEED NP  -> NP random descents that reach level L: "PREFIX hi lo"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
typedef struct { int lv, wt, m, nbad; u64 flo[16], fhi[16]; int fc[16]; unsigned char *isbad; } Cn;
static int N, NL, NC, vs[64]; static Cn *C; static int *byl[64], nbyl[64];
static long long nodes[64], kids[64], nsol;
static u64 alo, ahi;
static int parity2(u64 a, u64 b) { return (__builtin_popcountll(a) + __builtin_popcountll(b)) & 1; }
static void setbits(int start, int k, u64 v) {   // assignment bits start..start+k-1 := v
    for (int j = 0; j < k; j++) {
        int b = start + j; int bit = (v >> j) & 1;
        if (b < 64) { alo &= ~(1ULL << b); alo |= (u64)bit << b; }
        else { ahi &= ~(1ULL << (b - 64)); ahi |= (u64)bit << (b - 64); }
    }
}
static int child_ok(int t) {
    for (int q = 0; q < nbyl[t]; q++) {
        Cn *X = &C[byl[t][q]]; int s = 0;
        for (int b = 0; b < X->m; b++) s |= (parity2(X->flo[b] & alo, X->fhi[b] & ahi) ^ X->fc[b]) << b;
        if (X->isbad[s]) return 0;
    }
    return 1;
}
static void dfs(int t) {
    if (t == NL) { nsol++; printf("SOLUTION %016llx%016llx\n", (unsigned long long)ahi, (unsigned long long)alo); return; }
    nodes[t]++;
    int k = vs[t + 1] - vs[t];
    for (u64 v = 0; v < (1ULL << k); v++) {
        setbits(vs[t], k, v);
        if (child_ok(t)) { kids[t]++; dfs(t + 1); }
    }
    setbits(vs[t], k, 0);
}
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d %d %d", &N, &NL, &NC) != 3) return 1;
    for (int t = 0; t <= NL; t++) if (fscanf(f, "%d", &vs[t]) != 1) return 1;
    C = calloc(NC, sizeof(Cn));
    for (int c = 0; c < NC; c++) {
        Cn *X = &C[c];
        if (fscanf(f, "%d %d %d %d", &X->lv, &X->wt, &X->m, &X->nbad) != 4) return 1;
        for (int b = 0; b < X->m; b++) {
            char hx[80]; if (fscanf(f, "%79s %d", hx, &X->fc[b]) != 2) return 1;
            int L = strlen(hx); u64 lo = 0, hi = 0;
            for (int i = 0; i < L; i++) {      // digit i from the right has weight 16^i
                char ch = hx[L - 1 - i]; int d = (ch >= '0' && ch <= '9') ? ch - '0' : (ch >= 'a' && ch <= 'f') ? ch - 'a' + 10 : -1;
                if (d < 0) { fprintf(stderr, "bad hex\n"); return 1; }
                int pos = 4 * i;
                if (pos < 64) lo |= (u64)d << pos; else hi |= (u64)d << (pos - 64);
                if (pos < 64 && pos + 4 > 64) hi |= (u64)d >> (64 - pos);
            }
            X->flo[b] = lo; X->fhi[b] = hi;
        }
        X->isbad = calloc(1 << X->m, 1);
        for (int q = 0; q < X->nbad; q++) { int b; if (fscanf(f, "%d", &b) != 1) return 1; if (b < 0 || b >= (1 << X->m)) return 3; X->isbad[b] = 1; }
        if (X->lv < 0 || X->lv >= NL) return 4;
        // variables used must be < vs[lv+1]
        for (int b = 0; b < X->m; b++) for (int j = vs[X->lv + 1]; j < 128; j++) {
            u64 w = j < 64 ? (X->flo[b] >> j) & 1 : (X->fhi[b] >> (j - 64)) & 1;
            if (w) { fprintf(stderr, "constraint %d uses variable %d above level\n", c, j); return 5; }
        }
    }
    fclose(f);
    for (int t = 0; t < NL; t++) { byl[t] = malloc(sizeof(int) * (NC + 1)); nbyl[t] = 0; }
    for (int c = 0; c < NC; c++) byl[C[c].lv][nbyl[C[c].lv]++] = c;
    if (argc > 2 && !strcmp(argv[2], "probe")) {
        int L = atoi(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL; long np = atol(argv[5]); long got = 0, tries = 0;
        while (got < np && tries < 100000000L) {
            tries++; alo = ahi = 0; int t = 0, dead = 0;
            while (t < L) {
                int k = vs[t + 1] - vs[t]; u64 nch = 1ULL << k;
                u64 *alive = malloc(sizeof(u64) * nch); u64 na = 0;
                for (u64 v = 0; v < nch; v++) { setbits(vs[t], k, v); if (child_ok(t)) alive[na++] = v; }
                if (!na) { free(alive); dead = 1; break; }
                setbits(vs[t], k, alive[rnd() % na]); free(alive); t++;
            }
            if (!dead) { printf("PREFIX %016llx %016llx\n", (unsigned long long)ahi, (unsigned long long)alo); got++; }
        }
        printf("PROBEDONE got %ld tries %ld\n", got, tries);
        return 0;
    }
    alo = ahi = 0; dfs(0);
    printf("DONE naive nsol %lld N %d\n", nsol, N);
    for (int t = 0; t < NL; t++) printf("LEVEL %d kt %d ncons %d nodes %lld kids %lld\n", t, vs[t + 1] - vs[t], nbyl[t], nodes[t], kids[t]);
    return 0;
}
