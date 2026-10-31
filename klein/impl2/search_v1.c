/*
 * Exhaustive search engine for symmetric bilinear forms B on Y (dim k <= 31) given in
 * gauge-fixed affine coordinates B = part + sum_s x_s H_s, variables grouped by "level"
 * (level t = first Gram row in which the variable occurs).  At level t the Gram row
 * R_t = (B(w_t, w_l))_l is determined; all constraint words y whose coordinate vector has
 * highest bit t are then checked:
 *     syndrome s_y = (B(y, x_j))_j  must avoid the bad set Bad(y).
 * For a node, s_y is an affine function of the level-t variables v: s_y(v) = s0 + L_y v.
 * Bad children {v : L_y v in s0 + Bad(y)} are computed by linear algebra and removed.
 *
 * Input file format (all integers, whitespace separated), see export.py.
 * Usage: search <instance file> [njobs job split_level] [maxsol]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;

#define MAXK 32
#define MAXKT 22

static int k, N;
static int vstart[MAXK + 1];
static int kt[MAXK];
/* row entries (t,l), l>=t : const bit and mask over variables */
static int ent_const[MAXK][MAXK];
static u128 ent_mask[MAXK][MAXK];
/* rlin[t][v] : contribution of level-t variables (value v) to row t */
static uint32_t *rlin[MAXK];

typedef struct {
    int level;
    uint32_t cmask;      /* coordinates of y in w-basis (bit t set) */
    int m;
    uint32_t d[32];      /* coordinates of basis x_j of Y_{S^c} */
    int nbad;
    /* elimination of L (m x kt) */
    int rho;
    int piv[32];         /* pivot bit of basis element i (decreasing order) */
    uint32_t bu[32];     /* basis element (m-bit) */
    uint32_t bc[32];     /* combination (kt-bit) */
    int kdim;            /* kernel dim */
    uint32_t *kspan;     /* 2^kdim kernel elements */
    /* bad list sorted by residual */
    uint32_t *bres;      /* residual of bad syndrome */
    uint32_t *bz;        /* Z(bad) */
    int w;               /* weight of y (for stats) */
} Con;

static Con *cons;
static int ncons;
static int *lev_start;   /* constraints sorted by level: [lev_start[t], lev_start[t+1]) */

static long long nodes[MAXK + 1], kids[MAXK + 1], coneval[MAXK + 1];
static long long nsol = 0, maxsol = -1;
static int njobs = 1, job = 0, split_level = -1;
static long long split_counter = 0;
static uint32_t R[MAXK];

static inline int par128(u128 x) {
    return __builtin_parityll((uint64_t)x) ^ __builtin_parityll((uint64_t)(x >> 64));
}

static void die(const char *s) { fprintf(stderr, "error: %s\n", s); exit(1); }

static int rd(FILE *f) {
    long long x;
    if (fscanf(f, "%lld", &x) != 1) die("read");
    return (int)x;
}
static uint32_t rdu(FILE *f) {
    unsigned long long x;
    if (fscanf(f, "%llu", &x) != 1) die("readu");
    return (uint32_t)x;
}

static int cmp_res(const void *a, const void *b, void *ctx);

static void prepare_con(Con *c, uint32_t *bad) {
    int t = c->level;
    int K = kt[t];
    /* columns of L: col_b = M r_b, r_b = rlin[t][1<<b] */
    c->rho = 0;
    c->kdim = 0;
    uint32_t kb[MAXKT];
    for (int b = 0; b < K; b++) {
        uint32_t rb = rlin[t][1u << b];
        uint32_t col = 0;
        for (int j = 0; j < c->m; j++)
            col |= (uint32_t)__builtin_parity(rb & c->d[j]) << j;
        uint32_t comb = 1u << b;
        /* reduce by basis (basis kept sorted by decreasing pivot) */
        for (int i = 0; i < c->rho; i++)
            if ((col >> c->piv[i]) & 1) { col ^= c->bu[i]; comb ^= c->bc[i]; }
        if (col == 0) {
            kb[c->kdim++] = comb;
        } else {
            int p = 31 - __builtin_clz(col);
            /* insert keeping decreasing pivot order; also need existing elements with pivot<p
               to not contain bit p? Not required: we reduce in decreasing order and each element's
               highest bit is its pivot. Insert position: */
            int pos = c->rho;
            while (pos > 0 && c->piv[pos - 1] < p) pos--;
            for (int i = c->rho; i > pos; i--) { c->piv[i] = c->piv[i - 1]; c->bu[i] = c->bu[i - 1]; c->bc[i] = c->bc[i - 1]; }
            c->piv[pos] = p; c->bu[pos] = col; c->bc[pos] = comb;
            c->rho++;
        }
    }
    c->kspan = malloc(sizeof(uint32_t) << c->kdim);
    c->kspan[0] = 0;
    for (int i = 0; i < c->kdim; i++)
        for (int j = 0; j < (1 << i); j++) c->kspan[(1 << i) + j] = c->kspan[j] ^ kb[i];
    /* residuals and Z of bad syndromes */
    c->bres = malloc(sizeof(uint32_t) * (c->nbad + 1));
    c->bz = malloc(sizeof(uint32_t) * (c->nbad + 1));
    uint64_t *tmp = malloc(sizeof(uint64_t) * (c->nbad + 1));
    for (int q = 0; q < c->nbad; q++) {
        uint32_t s = bad[q], z = 0;
        for (int i = 0; i < c->rho; i++)
            if ((s >> c->piv[i]) & 1) { s ^= c->bu[i]; z ^= c->bc[i]; }
        tmp[q] = ((uint64_t)s << 32) | z;
    }
    /* sort by residual */
    for (int a = 1; a < c->nbad; a++) {
        uint64_t x = tmp[a]; int b = a - 1;
        while (b >= 0 && tmp[b] > x) { tmp[b + 1] = tmp[b]; b--; }
        tmp[b + 1] = x;
    }
    for (int q = 0; q < c->nbad; q++) { c->bres[q] = (uint32_t)(tmp[q] >> 32); c->bz[q] = (uint32_t)tmp[q]; }
    free(tmp);
}

static void report(u128 X) {
    nsol++;
    printf("SOL");
    for (int s = 0; s < N; s++) printf(" %d", (int)((X >> s) & 1));
    printf("\n");
    fflush(stdout);
    if (maxsol >= 0 && nsol >= maxsol) {
        fprintf(stderr, "maxsol reached\n");
        exit(0);
    }
}

static void dfs(int t, u128 X) {
    if (t == k) { report(X); return; }
    if (t == split_level) {
        long long c = split_counter++;
        if (c % njobs != job) return;
    }
    nodes[t]++;
    uint32_t R0 = 0;
    for (int l = 0; l < t; l++) R0 |= ((R[l] >> t) & 1u) << l;
    for (int l = t; l < k; l++) R0 |= (uint32_t)(ent_const[t][l] ^ par128(ent_mask[t][l] & X)) << l;
    int K = kt[t];
    int nk = 1 << K;
    int nw = (nk + 63) >> 6;
    uint64_t alive[1 << (MAXKT - 6)];
    for (int i = 0; i < nw; i++) alive[i] = ~0ULL;
    if (nk & 63) alive[nw - 1] = (1ULL << (nk & 63)) - 1;
    long long nalive = nk;
    for (int ci = lev_start[t]; ci < lev_start[t + 1]; ci++) {
        Con *c = &cons[ci];
        coneval[t]++;
        uint32_t A = R0;
        uint32_t cm = c->cmask & ~(1u << t);
        while (cm) { int i = __builtin_ctz(cm); cm &= cm - 1; A ^= R[i]; }
        uint32_t s = 0;
        for (int j = 0; j < c->m; j++) s |= (uint32_t)__builtin_parity(A & c->d[j]) << j;
        uint32_t z = 0;
        for (int i = 0; i < c->rho; i++)
            if ((s >> c->piv[i]) & 1) { s ^= c->bu[i]; z ^= c->bc[i]; }
        /* binary search residual s in bres */
        int lo = 0, hi = c->nbad;
        while (lo < hi) { int mid = (lo + hi) >> 1; if (c->bres[mid] < s) lo = mid + 1; else hi = mid; }
        int killed_any = 0;
        for (int q = lo; q < c->nbad && c->bres[q] == s; q++) {
            uint32_t v0 = z ^ c->bz[q];
            int nks = 1 << c->kdim;
            for (int e = 0; e < nks; e++) {
                uint32_t v = v0 ^ c->kspan[e];
                alive[v >> 6] &= ~(1ULL << (v & 63));
            }
            killed_any = 1;
        }
        if (killed_any) {
            nalive = 0;
            for (int i = 0; i < nw; i++) nalive += __builtin_popcountll(alive[i]);
            if (nalive == 0) return;
        }
    }
    kids[t] += nalive;
    for (int i = 0; i < nw; i++) {
        uint64_t a = alive[i];
        while (a) {
            int b = __builtin_ctzll(a); a &= a - 1;
            uint32_t v = (uint32_t)(i * 64 + b);
            R[t] = R0 ^ rlin[t][v];
            dfs(t + 1, X | ((u128)v << vstart[t]));
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 2) die("usage");
    if (argc >= 5) { njobs = atoi(argv[2]); job = atoi(argv[3]); split_level = atoi(argv[4]); }
    if (argc >= 6) maxsol = atoll(argv[5]);
    FILE *f = fopen(argv[1], "r");
    if (!f) die("open");
    k = rd(f); N = rd(f);
    if (k > MAXK || N > 128) die("size");
    for (int t = 0; t <= k; t++) vstart[t] = rd(f);
    for (int t = 0; t < k; t++) { kt[t] = vstart[t + 1] - vstart[t]; if (kt[t] > MAXKT) die("kt too big"); }
    /* entries: for t, for l>=t: const, then mask as list: count then indices */
    for (int t = 0; t < k; t++)
        for (int l = t; l < k; l++) {
            ent_const[t][l] = rd(f);
            int cnt = rd(f);
            u128 m = 0;
            for (int q = 0; q < cnt; q++) { int s = rd(f); m |= (u128)1 << s; }
            ent_mask[t][l] = m;
        }
    /* rlin: from masks restricted to level-t variables */
    for (int t = 0; t < k; t++) {
        int K = kt[t];
        uint32_t rb[MAXKT];
        for (int b = 0; b < K; b++) {
            rb[b] = 0;
            for (int l = t; l < k; l++)
                if ((ent_mask[t][l] >> (vstart[t] + b)) & 1) rb[b] |= 1u << l;
        }
        rlin[t] = malloc(sizeof(uint32_t) << K);
        rlin[t][0] = 0;
        for (int b = 0; b < K; b++)
            for (int j = 0; j < (1 << b); j++) rlin[t][(1 << b) + j] = rlin[t][j] ^ rb[b];
        /* sanity: entries of row t must not depend on variables of level > t */
        for (int l = t; l < k; l++) {
            u128 m = ent_mask[t][l];
            for (int s = vstart[t + 1]; s < N; s++)
                if ((m >> s) & 1) die("entry depends on later variable");
        }
    }
    ncons = rd(f);
    cons = calloc(ncons, sizeof(Con));
    lev_start = calloc(k + 1, sizeof(int));
    int prevlev = -1;
    for (int i = 0; i < ncons; i++) {
        Con *c = &cons[i];
        c->level = rd(f);
        if (c->level < prevlev) die("constraints not sorted by level");
        prevlev = c->level;
        c->w = rd(f);
        c->cmask = rdu(f);
        if (31 - __builtin_clz(c->cmask) != c->level) die("cmask level mismatch");
        c->m = rd(f);
        if (c->m > 31) die("m too big");
        for (int j = 0; j < c->m; j++) c->d[j] = rdu(f);
        c->nbad = rd(f);
        uint32_t *bad = malloc(sizeof(uint32_t) * (c->nbad + 1));
        for (int q = 0; q < c->nbad; q++) bad[q] = rdu(f);
        prepare_con(c, bad);
        free(bad);
    }
    fclose(f);
    {
        int ci = 0;
        for (int t = 0; t <= k; t++) {
            while (ci < ncons && cons[ci].level < t) ci++;
            lev_start[t] = ci;
        }
        lev_start[k] = ncons;
    }
    clock_t t0 = clock();
    dfs(0, 0);
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    fprintf(stderr, "done nsol %lld cpu %.2f\n", nsol, secs);
    printf("STATS nsol %lld cpu %.3f njobs %d job %d split %d\n", nsol, secs, njobs, job, split_level);
    for (int t = 0; t < k; t++)
        printf("LEVEL %d kt %d ncons %d nodes %lld kids %lld coneval %lld\n", t, kt[t],
               lev_start[t + 1] - lev_start[t], nodes[t], kids[t], coneval[t]);
    printf("END\n");
    return 0;
}
