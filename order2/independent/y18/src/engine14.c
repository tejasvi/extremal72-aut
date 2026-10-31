/* Generic DFS over F2 variables v_0..v_{nv-1} (nv <= 128) with syndrome constraints.
 * Each constraint (word) has m syndrome bits s_j = c_j + parity(A_j & v); forbidden set given as bitmap.
 * Events (depth d, word, basis of V_d, dead table): after d variables are assigned (others 0), the set of
 * possible syndromes is the coset base + V_d; it is reduced modulo the (fully reduced) basis of V_d and
 * looked up in the dead table (cosets all of whose elements are forbidden); prune if dead.
 *
 * usage: engine DATA MODE [args]
 *   MODE full                 : DFS from depth 0 (whole space); prints node counts and solutions
 *   MODE prefixes FILE D      : FILE has lines "hi lo" (hex, 128-bit assignment of the first D variables);
 *                               DFS below each prefix
 *   MODE knuth NPROBES SEED   : Knuth random-probe estimate of the full tree size from depth 0
 *   MODE knuthpre FILE D NPROBES SEED : Knuth estimate below each prefix in FILE (averaged over prefixes)
 * Solutions are printed as "SOL hi lo".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

typedef struct { uint64_t lo, hi; } u128;

typedef struct {
    int m;
    uint32_t c;
    u128 A[16];
} Word;

typedef struct {
    int d, w, r;
    uint32_t fb[16];
    uint8_t *dead;
    uint32_t col;   /* syndrome change of word w when variable d-1 flips (column d-1 of its matrix) */
} Event;

static int nv, nw, ne;
static Word *W;
static Event *EV;
static int *ev_start; /* events with depth d are EV[ev_start[d] .. ev_start[d+1]-1] */
static long long nodes[130];
static long long nsol = 0;
static u128 cur;
static int dmax = -1;          /* depth at which a node counts as a leaf (default nv) */
static int stop_first = 0;     /* stop the current DFS at the first leaf */
static int found = 0;
static Event *EV_all; static int ne_all; static char *active = NULL;
static long long *evkill;   /* kill counters of the events (engine13, depths > D2 re-sorting) */

static inline int par128(u128 a, u128 b) {
    return __builtin_parityll((a.lo & b.lo) ^ (a.hi & b.hi));
}

static inline uint32_t syndrome(const Word *w, u128 v) {
    uint32_t s = w->c;
    for (int j = 0; j < w->m; j++) s ^= (uint32_t)par128(w->A[j], v) << j;
    return s;
}


/* returns 1 if all events at depth d pass */
static int check_depth(int d, u128 v) {
    for (int e = ev_start[d]; e < ev_start[d + 1]; e++) {
        const Event *ev = &EV[e];
        uint32_t s = syndrome(&W[ev->w], v);
        for (int i = 0; i < ev->r; i++) {
            uint32_t b = ev->fb[i];
            if (s & b & (~b + 1)) s ^= b;   /* pivot = lowest set bit of b */
        }
        if ((ev->dead[s >> 3] >> (s & 7)) & 1) return 0;
    }
    return 1;
}

static void setbit(u128 *v, int i, int b) {
    if (i < 64) { if (b) v->lo |= 1ULL << i; else v->lo &= ~(1ULL << i); }
    else { if (b) v->hi |= 1ULL << (i - 64); else v->hi &= ~(1ULL << (i - 64)); }
}

static FILE *solf = NULL;

static void dfs(int d) {
    nodes[d]++;
    if (d == dmax) {
        nsol++;
        found = 1;
        if (dmax == nv) {
            printf("SOL %016llx %016llx\n", (unsigned long long)cur.hi, (unsigned long long)cur.lo);
            fflush(stdout);
        }
        return;
    }
    /* events at depth d+1 for both values of variable d: s(bit d = 1) = s(bit d = 0) ^ col */
    setbit(&cur, d, 0);
    int ok0 = 1, ok1 = 1;
    for (int e = ev_start[d + 1]; e < ev_start[d + 2] && (ok0 | ok1); e++) {
        const Event *ev = &EV[e];
        uint32_t s0 = syndrome(&W[ev->w], cur);
        uint32_t s1 = s0 ^ ev->col;
        for (int i = 0; i < ev->r; i++) {
            uint32_t b = ev->fb[i], lowb = b & (~b + 1);
            if (s0 & lowb) s0 ^= b;
            if (s1 & lowb) s1 ^= b;
        }
        if (ok0 && ((ev->dead[s0 >> 3] >> (s0 & 7)) & 1)) { ok0 = 0; if (evkill) evkill[e]++; }
        if (ok1 && ((ev->dead[s1 >> 3] >> (s1 & 7)) & 1)) { ok1 = 0; if (evkill) evkill[e]++; }
    }
    if (ok0) dfs(d + 1);
    if (ok1 && !(stop_first && found)) {
        setbit(&cur, d, 1);
        dfs(d + 1);
        setbit(&cur, d, 0);
    }
}

/* Knuth estimator: one random probe from depth d0 with prefix cur; returns estimated subtree size,
 * accumulates per-depth estimates into est[] */
static double est[130];
static uint64_t rng_state;
static inline uint64_t rng(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state;
}
static double knuth_probe(int d0) {
    double weight = 1.0, total = 0.0;
    u128 v = cur;
    for (int d = d0; ; d++) {
        est[d] += weight;
        total += weight;
        if (d == nv) break;
        int okb[2], cnt = 0;
        for (int b = 0; b < 2; b++) {
            setbit(&v, d, b);
            okb[b] = check_depth(d + 1, v);
            cnt += okb[b];
        }
        if (cnt == 0) break;
        int b;
        if (cnt == 2) b = rng() & 1; else b = okb[1];
        setbit(&v, d, b);
        weight *= cnt;
    }
    return total;
}

static void load(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(1); }
    char magic[4];
    if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "Y39F", 4)) { fprintf(stderr, "bad magic\n"); exit(1); }
    if (fread(&nv, 4, 1, f) != 1 || fread(&nw, 4, 1, f) != 1 || fread(&ne, 4, 1, f) != 1) exit(1);
    W = calloc(nw, sizeof(Word));
    for (int i = 0; i < nw; i++) {
        if (fread(&W[i].m, 4, 1, f) != 1 || fread(&W[i].c, 4, 1, f) != 1) exit(1);
        if (W[i].m > 16) { fprintf(stderr, "m too large\n"); exit(1); }
        for (int j = 0; j < W[i].m; j++) {
            uint64_t lo, hi;
            if (fread(&lo, 8, 1, f) != 1 || fread(&hi, 8, 1, f) != 1) exit(1);
            W[i].A[j].lo = lo; W[i].A[j].hi = hi;
        }
    }
    EV = calloc(ne, sizeof(Event));
    for (int i = 0; i < ne; i++) {
        int32_t hdr[3];
        if (fread(hdr, 4, 3, f) != 3) exit(1);
        EV[i].d = hdr[0]; EV[i].w = hdr[1]; EV[i].r = hdr[2];
        if (EV[i].r > 16 || EV[i].w < 0 || EV[i].w >= nw) { fprintf(stderr, "bad event\n"); exit(1); }
        if (EV[i].r > 0 && (int)fread(EV[i].fb, 4, EV[i].r, f) != EV[i].r) exit(1);
        int m = W[EV[i].w].m;
        int nb = (1 << m) / 8; if (nb < 1) nb = 1;
        EV[i].dead = malloc(nb);
        if ((int)fread(EV[i].dead, 1, nb, f) != nb) exit(1);
        EV[i].col = 0;
        if (EV[i].d >= 1) {
            int var = EV[i].d - 1;
            for (int j = 0; j < m; j++) {
                u128 a = W[EV[i].w].A[j];
                int bit = var < 64 ? (int)((a.lo >> var) & 1) : (int)((a.hi >> (var - 64)) & 1);
                EV[i].col |= (uint32_t)bit << j;
            }
        }
    }
    fclose(f);
    ev_start = calloc(nv + 2, sizeof(int));
    int e = 0;
    for (int d = 0; d <= nv + 1; d++) {
        while (e < ne && EV[e].d < d) e++;
        ev_start[d] = e;
    }
    for (int i = 1; i < ne; i++) if (EV[i].d < EV[i - 1].d) { fprintf(stderr, "events not sorted\n"); exit(1); }
    fprintf(stderr, "loaded nv=%d nw=%d ne=%d\n", nv, nw, ne);
    ne_all = ne;
    EV_all = malloc(sizeof(Event) * (ne > 0 ? ne : 1));
    memcpy(EV_all, EV, sizeof(Event) * ne);
}

static void apply_mask(void) {
    ne = 0;
    for (int i = 0; i < ne_all; i++) if (!active || active[EV_all[i].w]) EV[ne++] = EV_all[i];
    int e = 0;
    for (int d = 0; d <= nv + 1; d++) {
        while (e < ne && EV[e].d < d) e++;
        ev_start[d] = e;
    }
}

/* check all events with depth <= D for prefix v (variables >= D are 0) */
static int check_prefix(int D, u128 v) {
    for (int d = 0; d <= D; d++) if (!check_depth(d, v)) return 0;
    return 1;
}


/* ---------- X-orbit representatives (Y39 separator) ----------
 * action file: int ng, int nx(=40); then for each group element: nx rows (uint64, bit j of row i = coefficient of
 * variable j in image variable i) and a constant (uint64): x' = M x + c. Z = variables 0..29 (image depends on Z only).
 */
static int ng_act, nx_act;
static long long stabhist[4096];
static uint64_t *act_rows, *act_cst;
static inline uint64_t act_apply(int g, uint64_t x) {
    uint64_t out = act_cst[g];
    const uint64_t *r = act_rows + (size_t)g * nx_act;
    for (int i = 0; i < nx_act; i++) out ^= (uint64_t)__builtin_parityll(r[i] & x) << i;
    return out;
}
static void xreps(const char *actfile, const char *gensfile, const char *outfile, int ZB, int WB) {
    FILE *f = fopen(actfile, "rb");
    if (!f || fread(&ng_act, 4, 1, f) != 1 || fread(&nx_act, 4, 1, f) != 1) { fprintf(stderr, "act read\n"); exit(1); }
    act_rows = malloc(sizeof(uint64_t) * ng_act * nx_act);
    act_cst = malloc(sizeof(uint64_t) * ng_act);
    for (int g = 0; g < ng_act; g++) {
        if ((int)fread(act_rows + (size_t)g * nx_act, 8, nx_act, f) != nx_act || fread(act_cst + g, 8, 1, f) != 1) exit(1);
    }
    fclose(f);
    int gens[64], ngen = 0;
    FILE *gf = fopen(gensfile, "r");
    while (ngen < 64 && fscanf(gf, "%d", &gens[ngen]) == 1) ngen++;
    fclose(gf);
    if (ZB > 32 || WB > 12 || ZB + WB != nx_act) { fprintf(stderr, "bad ZB/WB\n"); exit(1); }
    const uint64_t ZM = (1ULL << ZB) - 1;
    const int NW = 1 << WB;
    /* byte tables for generators on Z: T[k][c][b] */
    static uint32_t T[64][4][256];
    uint32_t zc[64];
    for (int k = 0; k < ngen; k++) {
        int g = gens[k];
        uint32_t col[32];
        for (int j = 0; j < ZB; j++) {
            uint32_t c = 0;
            for (int i = 0; i < ZB; i++) if ((act_rows[(size_t)g * nx_act + i] >> j) & 1) c |= 1u << i;
            col[j] = c;
            if (act_rows[(size_t)g * nx_act] >> 63) {} /* unused */
        }
        for (int c = 0; c < 4; c++)
            for (int b = 0; b < 256; b++) {
                uint32_t v = 0;
                for (int t = 0; t < 8; t++) if ((b >> t) & 1 && 8 * c + t < ZB) v ^= col[8 * c + t];
                T[k][c][b] = v;
            }
        zc[k] = (uint32_t)(act_cst[g] & ZM);
    }
    uint64_t *vis = calloc(((1ULL << ZB) + 63) / 64, 8);
    uint32_t *queue = malloc(sizeof(uint32_t) * (ng_act + 16));
    FILE *of = fopen(outfile, "w");
    long long norb = 0, nzvalid = 0, nxcand = 0, nxrep = 0;
    double sum_valid_orbit = 0;
    static int parent[4096], rep[4096];
    for (uint64_t z0 = 0; z0 < (1ULL << ZB); z0++) {
        if ((vis[z0 >> 6] >> (z0 & 63)) & 1) continue;
        /* BFS orbit of z0 under generators */
        int qh = 0, qt = 0;
        queue[qt++] = (uint32_t)z0; vis[z0 >> 6] |= 1ULL << (z0 & 63);
        while (qh < qt) {
            uint32_t z = queue[qh++];
            for (int k = 0; k < ngen; k++) {
                uint32_t w = zc[k] ^ T[k][0][z & 255] ^ T[k][1][(z >> 8) & 255] ^ T[k][2][(z >> 16) & 255] ^ T[k][3][(z >> 24) & 255];
                if (!((vis[w >> 6] >> (w & 63)) & 1)) {
                    vis[w >> 6] |= 1ULL << (w & 63);
                    if (qt >= ng_act) { fprintf(stderr, "orbit larger than group!\n"); exit(1); }
                    queue[qt++] = w;
                }
            }
        }
        int osize = qt;
        if (ng_act % osize) { fprintf(stderr, "orbit size does not divide |G|\n"); exit(1); }
        norb++;
        cur.lo = z0; cur.hi = 0;
        if (!check_prefix(ZB, cur)) continue;
        nzvalid++;
        /* stabilizer of z0 */
        int stab[64000], ns = 0;
        if (osize == ng_act) { stab[ns++] = 0; }
        else for (int g = 0; g < ng_act; g++) if ((act_apply(g, z0) & ZM) == z0) stab[ns++] = g;
        if (ns * osize != ng_act) { fprintf(stderr, "stabilizer size mismatch %d %d\n", ns, osize); exit(1); }
        /* orbits of stab on w = (beta, alpha) in F2^10 */
        for (int w = 0; w < NW; w++) parent[w] = w;
        for (int t = 0; t < ns; t++) {
            int g = stab[t];
            if (g == 0) continue;
            for (int w = 0; w < NW; w++) {
                uint64_t x = z0 | ((uint64_t)w << ZB);
                uint64_t y = act_apply(g, x);
                if ((y & ZM) != z0) { fprintf(stderr, "stab element moves z\n"); exit(1); }
                int a = w, b = (int)(y >> ZB);
                while (parent[a] != a) a = parent[a];
                while (parent[b] != b) b = parent[b];
                if (a != b) { if (a < b) parent[b] = a; else parent[a] = b; }
            }
        }
        for (int w = 0; w < NW; w++) { int a = w; while (parent[a] != a) a = parent[a]; rep[w] = a; }
        for (int w = 0; w < NW; w++) {
            if (rep[w] != w) continue;   /* rep = minimum of its class (union by smaller root) */
            nxcand++;
            uint64_t x = z0 | ((uint64_t)w << ZB);
            cur.lo = x; cur.hi = 0;
            int okx = 1;
            for (int d = ZB + 1; d <= ZB + WB && okx; d++) okx = check_depth(d, cur);   /* depths <= ZB passed for z0 */
            if (!okx) continue;
            /* |Stab_G(x)| = #{g in stab : g fixes w} */
            int sx = 0;
            for (int t = 0; t < ns; t++) { if (stab[t] == 0 || act_apply(stab[t], x) == x) sx++; }
            int cls = 0; for (int u = 0; u < NW; u++) if (rep[u] == w) cls++;
            if (osize * cls * sx != ng_act) { fprintf(stderr, "orbit-stabilizer mismatch\n"); exit(1); }
            fprintf(of, "0 %llx\n", (unsigned long long)x);
            if (sx < 4096) stabhist[sx]++;
            nxrep++;
            sum_valid_orbit += (double)ng_act / sx;
        }
    }
    fclose(of);
    printf("XREPS zorbits %lld zvalid %lld xcand %lld xreps %lld sum_orbit_sizes %.0f\n", norb, nzvalid, nxcand, nxrep, sum_valid_orbit);
    printf("STABHIST");
    for (int i = 1; i < 4096; i++) if (stabhist[i]) printf(" %d:%lld", i, stabhist[i]);
    printf("\n");
}


/* canon ACTFILE CANONFILE INFILE OUTPREFIX
 * CANONFILE: nwords, then per word: class g canon_index, then 5 lines "mask const" (a_w component j = parity(mask & x) ^ const)
 * For each prefix x ("hi lo" lines, hi = 0): the words w with a_w(x) = 0. If exactly one, x' = A_g(x) with g = g_w,
 * checked to have exactly the canonical word as its kernel; written to OUTPREFIX_c<class>.txt; else OUTPREFIX_other.txt. */
static void canon(const char *actfile, const char *canonfile, const char *infile, const char *outprefix) {
    FILE *f = fopen(actfile, "rb");
    if (!f || fread(&ng_act, 4, 1, f) != 1 || fread(&nx_act, 4, 1, f) != 1) { fprintf(stderr, "act read\n"); exit(1); }
    act_rows = malloc(sizeof(uint64_t) * ng_act * nx_act);
    act_cst = malloc(sizeof(uint64_t) * ng_act);
    for (int g = 0; g < ng_act; g++)
        if ((int)fread(act_rows + (size_t)g * nx_act, 8, nx_act, f) != nx_act || fread(act_cst + g, 8, 1, f) != 1) exit(1);
    fclose(f);
    FILE *cf = fopen(canonfile, "r");
    int nwd;
    if (fscanf(cf, "%d", &nwd) != 1 || nwd > 256) exit(1);
    static int wcls[256], wg[256], wcan[256];
    static unsigned long long wm[256][5]; static int wc[256][5];
    int ncls = 0;
    for (int i = 0; i < nwd; i++) {
        if (fscanf(cf, "%d %d %d", &wcls[i], &wg[i], &wcan[i]) != 3) exit(1);
        if (wcls[i] + 1 > ncls) ncls = wcls[i] + 1;
        for (int j = 0; j < 5; j++) if (fscanf(cf, "%llx %d", &wm[i][j], &wc[i][j]) != 2) exit(1);
    }
    fclose(cf);
    FILE *outs[64]; char path[1024];
    for (int c = 0; c < ncls; c++) { snprintf(path, sizeof path, "%s_c%d.txt", outprefix, c); outs[c] = fopen(path, "w"); }
    snprintf(path, sizeof path, "%s_other.txt", outprefix); FILE *oth = fopen(path, "w");
    FILE *in = fopen(infile, "r");
    unsigned long long hi, lo;
    long long cnt[65] = {0}, nin = 0;
    while (fscanf(in, "%llx %llx", &hi, &lo) == 2) {
        nin++;
        int k = -1, nk = 0;
        for (int i = 0; i < nwd; i++) {
            int z = 1;
            for (int j = 0; j < 5 && z; j++) z = ((__builtin_parityll(wm[i][j] & lo) ^ wc[i][j]) == 0);
            if (z) { k = i; nk++; }
        }
        if (nk != 1) { fprintf(oth, "0 %llx\n", lo); cnt[64]++; continue; }
        uint64_t x2 = act_apply(wg[k], lo);
        int k2 = -1, nk2 = 0;
        for (int i = 0; i < nwd; i++) {
            int z = 1;
            for (int j = 0; j < 5 && z; j++) z = ((__builtin_parityll(wm[i][j] & x2) ^ wc[i][j]) == 0);
            if (z) { k2 = i; nk2++; }
        }
        if (nk2 != 1 || k2 != wcan[k]) { fprintf(stderr, "canonicalization check failed\n"); exit(1); }
        fprintf(outs[wcls[k]], "0 %llx\n", (unsigned long long)x2);
        cnt[wcls[k]]++;
    }
    fclose(in);
    for (int c = 0; c < ncls; c++) fclose(outs[c]);
    fclose(oth);
    printf("CANON in %lld", nin);
    for (int c = 0; c < ncls; c++) printf(" class%d %lld", c, cnt[c]);
    printf(" other %lld\n", cnt[64]);
}


/* ---------- join mode ----------
 * Variables [D0,D1) = block 1, [D1,D2) = block 2. Phase 1: DFS over block 1 with all events at depths <= D1 -> S1.
 * Phase 2 (only if S1 nonempty): DFS over block 2 with block-1 variables 0, using only events at depths in (D1,D2]
 * of words whose syndrome rows have no coefficient on block-1 variables -> S2. Phase 3: for every (s1, s2), check
 * all events at depths (D1,D2]; survivors continue with the ordinary DFS from D2 (all events, counted in nodes[]).
 * nodes[d] for d <= D1 and d >= D2 equal those of the plain DFS. */
static int *ev2_start;   /* phase-2 event lists: indices into EV2 */
static Event *EV2;
static long long nodes2[130];
typedef struct { u128 *a; long long n, cap; } AList;
static void alist_push(AList *L, u128 v) {
    if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 1024; L->a = realloc(L->a, sizeof(u128) * L->cap); }
    L->a[L->n++] = v;
}
static AList S1, S2;
static int jD1, jD2;
static void dfs_collect(int d, int dstop, const Event *E, const int *es, long long *cnt, AList *out) {
    cnt[d]++;
    if (d == dstop) { alist_push(out, cur); return; }
    setbit(&cur, d, 0);
    int ok0 = 1, ok1 = 1;
    for (int e = es[d + 1]; e < es[d + 2] && (ok0 | ok1); e++) {
        const Event *ev = &E[e];
        uint32_t s0 = syndrome(&W[ev->w], cur);
        uint32_t s1 = s0 ^ ev->col;
        for (int i = 0; i < ev->r; i++) {
            uint32_t b = ev->fb[i], lowb = b & (~b + 1);
            if (s0 & lowb) s0 ^= b;
            if (s1 & lowb) s1 ^= b;
        }
        if ((ev->dead[s0 >> 3] >> (s0 & 7)) & 1) ok0 = 0;
        if ((ev->dead[s1 >> 3] >> (s1 & 7)) & 1) ok1 = 0;
    }
    if (ok0) dfs_collect(d + 1, dstop, E, es, cnt, out);
    if (ok1) { setbit(&cur, d, 1); dfs_collect(d + 1, dstop, E, es, cnt, out); setbit(&cur, d, 0); }
}
/* engine13: cross events = events at depths (D1,D2] whose word depends on block 1. A pair (s1, s2) passes all events
 * at depths (D1,D2] iff it passes the cross events: the other events (phase 2) only see block-2 and separator bits,
 * and every s2 in S2 passed them in phase 2. */
static int *ev3 = NULL, n3 = 0;
/* events at depths > D2: kill counters; every RESORT_EVERY passing pairs the events of each depth > D2 are re-sorted
 * by kill count (descending). The order of the events within a depth does not change which children survive. */
static long long *evkill = NULL;
static long long npass_total = 0;
#define RESORT_EVERY 65536
typedef struct { long long k; Event e; } EvK;
static int cmp_evk(const void *p, const void *q) {
    long long a = ((const EvK *)p)->k, b = ((const EvK *)q)->k;
    return a < b ? 1 : a > b ? -1 : 0;
}
static void resort_deep(int dfrom) {
    for (int d = dfrom + 1; d <= nv; d++) {
        int a = ev_start[d], b = ev_start[d + 1], n = b - a;
        if (n < 2) continue;
        EvK *t = malloc(sizeof(EvK) * n);
        for (int i = 0; i < n; i++) { t[i].k = evkill[a + i]; t[i].e = EV[a + i]; }
        qsort(t, n, sizeof(EvK), cmp_evk);
        for (int i = 0; i < n; i++) { EV[a + i] = t[i].e; evkill[a + i] = t[i].k / 2; }
        free(t);
    }
}
static void join_setup(int D0, int D1, int D2) {
    jD1 = D1; jD2 = D2;
    if (!evkill) evkill = calloc(ne + 1, sizeof(long long));   /* engine14: resort_deep needs it in every join mode */
    u128 m1 = {0, 0};
    for (int i = D0; i < D1; i++) setbit(&m1, i, 1);
    char *dep1 = calloc(nw, 1);
    for (int w = 0; w < nw; w++)
        for (int j = 0; j < W[w].m; j++)
            if ((W[w].A[j].lo & m1.lo) | (W[w].A[j].hi & m1.hi)) dep1[w] = 1;
    int n2 = 0;
    EV2 = malloc(sizeof(Event) * (ne + 1));
    for (int e = ev_start[D1 + 1]; e < ev_start[D2 + 1]; e++) if (!dep1[EV[e].w]) EV2[n2++] = EV[e];
    ev2_start = calloc(nv + 2, sizeof(int));
    int e = 0;
    for (int d = 0; d <= nv + 1; d++) { while (e < n2 && EV2[e].d < d) e++; ev2_start[d] = e; }
    int ndep = 0; for (int w = 0; w < nw; w++) ndep += dep1[w];
    n3 = 0; ev3 = malloc(sizeof(int) * (ne + 1));
    for (int e = ev_start[D1 + 1]; e < ev_start[D2 + 1]; e++) if (dep1[EV[e].w]) ev3[n3++] = e;
    for (int w = 0; w < nw; w++) if (W[w].m > 16) { fprintf(stderr, "syndrome wider than 16 bits\n"); exit(1); }
    fprintf(stderr, "join: block1 [%d,%d) block2 [%d,%d): %d words depend on block 1; phase-2 events %d of %d\n",
            D0, D1, D1, D2, ndep, n2, ev_start[D2 + 1] - ev_start[D1 + 1]);
}
#define KPRE 12
static inline uint32_t reduce_ev(const Event *ev, uint32_t v) {
    for (int i = 0; i < ev->r; i++) { uint32_t b = ev->fb[i]; if (v & b & (~b + 1)) v ^= b; }
    return v;
}
static inline int dead_after(const Event *ev, uint32_t v) {
    for (int i = 0; i < ev->r; i++) { uint32_t b = ev->fb[i]; if (v & b & (~b + 1)) v ^= b; }
    return (ev->dead[v >> 3] >> (v & 7)) & 1;
}
/* joinsplit: the pair phase takes only the rows i of S1 with i % split_n == split_k (split_n = 1: all rows).
 * p1_mark = sum of nodes[] right after phase 1, so that phase-1 nodes and pair-phase nodes can be reported apart. */
static long long split_n = 1, split_k = 0, p1_mark = 0;
static long long nodes_sum(void) { long long s = 0; for (int d = 0; d <= nv; d++) s += nodes[d]; return s; }
/* joinstab: Stab(X) reduction on the block variables (maps from stab_maps.py; h bit k = var 36+k, h' bit k = var 70+k).
 * phi_g (g preserving the halves): h -> h-part of B^g, depends on (x, h) only; psi_g (g swapping the halves):
 * h' -> h-part of B^g, depends on (x, h') only. In every Stab(X)-orbit of solutions the member with minimal h has
 * phi_g(h) >= h for all phi and h <= mu(h') = min over psi of psi(h'). Phase 1 keeps the rows of S1 with
 * phi_g(h) >= h for all g; S2 is sorted by mu descending and row h meets only the j with mu_j >= h.
 * dump_pairs: print each pair passing all events at depths (D1,D2] as "PP h h'" instead of the DFS below D2. */
typedef struct { uint64_t t[5][256]; } AffMap;
static AffMap *stP = NULL, *stS = NULL;
static int st_nh = 0, st_ns = 0, use_stab = 0, dump_pairs = 0;
static long long n1kept = 0;
static uint64_t *mu2 = NULL;
static inline uint64_t hpart(u128 v) { return (v.lo >> 36) | ((v.hi & 0x3FULL) << 28); }
static inline uint64_t h2part(u128 v) { return (v.hi >> 6) & ((1ULL << 34) - 1); }
static inline uint64_t aff_apply(const AffMap *m, uint64_t h) {
    return m->t[0][h & 255] ^ m->t[1][(h >> 8) & 255] ^ m->t[2][(h >> 16) & 255] ^ m->t[3][(h >> 24) & 255]
         ^ m->t[4][(h >> 32) & 255];
}
static void aff_build(AffMap *m, uint64_t c, const uint64_t *col) {
    for (int b = 0; b < 5; b++)
        for (int v = 0; v < 256; v++) {
            uint64_t y = b == 0 ? c : 0;
            for (int q = 0; q < 8; q++) if (((v >> q) & 1) && 8 * b + q < 34) y ^= col[8 * b + q];
            m->t[b][v] = y;
        }
}
/* stab file: blocks "X x nh ns", nh lines "P c col_0..col_33", ns lines "S c col_0..col_33" (hex) */
typedef struct { uint64_t x; int nh, ns; AffMap *P, *S; } StabBlock;
static StabBlock *stb = NULL; static int nstb = 0;
static void load_stab(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "stab file missing\n"); exit(1); }
    char tag[8]; unsigned long long x; int nh, ns;
    while (fscanf(f, "%7s %llx %d %d", tag, &x, &nh, &ns) == 4) {
        if (strcmp(tag, "X")) { fprintf(stderr, "stab file format\n"); exit(1); }
        stb = realloc(stb, sizeof(StabBlock) * (nstb + 1));
        StabBlock *B = &stb[nstb++];
        B->x = x; B->nh = nh; B->ns = ns;
        B->P = malloc(sizeof(AffMap) * (nh + 1)); B->S = malloc(sizeof(AffMap) * (ns + 1));
        for (int g = 0; g < nh + ns; g++) {
            unsigned long long c, col[34]; char t2[8];
            if (fscanf(f, "%7s %llx", t2, &c) != 2) { fprintf(stderr, "stab file short\n"); exit(1); }
            for (int k = 0; k < 34; k++) if (fscanf(f, "%llx", &col[k]) != 1) { fprintf(stderr, "stab file short\n"); exit(1); }
            if (strcmp(t2, g < nh ? "P" : "S")) { fprintf(stderr, "stab file map tag\n"); exit(1); }
            aff_build(g < nh ? &B->P[g] : &B->S[g - nh], c, (const uint64_t *)col);
        }
    }
    fclose(f);
    fprintf(stderr, "stab file: %d blocks\n", nstb);
}
static void select_stab(uint64_t x) {
    for (int b = 0; b < nstb; b++)
        if (stb[b].x == x) { st_nh = stb[b].nh; st_ns = stb[b].ns; stP = stb[b].P; stS = stb[b].S; return; }
    fprintf(stderr, "no stab block for %llx\n", (unsigned long long)x); exit(1);
}
typedef struct { uint64_t mu; u128 a; } MuEnt;
static int cmp_mu_desc(const void *p, const void *q) {
    uint64_t a = ((const MuEnt *)p)->mu, b = ((const MuEnt *)q)->mu;
    return a < b ? 1 : a > b ? -1 : 0;
}
/* number of j with mu2[j] >= h (mu2 sorted descending); all of S2 without swapping maps */
static inline long long jlimit(uint64_t h) {
    if (!use_stab || st_ns == 0) return S2.n;
    long long lo = 0, hi = S2.n;
    while (lo < hi) { long long m = (lo + hi) / 2; if (mu2[m] >= h) lo = m + 1; else hi = m; }
    return lo;
}
static void join_one(u128 x, int D0, long long *np1, long long *np2, long long *npair, long long *npass) {
    S1.n = 0; S2.n = 0;
    cur = x;
    dfs_collect(D0, jD1, EV, ev_start, nodes, &S1);
    p1_mark = nodes_sum();
    *np1 = S1.n; *np2 = 0; *npair = 0; *npass = 0;
    if (use_stab && st_nh > 0) {
        long long w = 0;
        for (long long i = 0; i < S1.n; i++) {
            uint64_t h = hpart(S1.a[i]);
            int keep = 1;
            for (int g = 0; g < st_nh && keep; g++) if (aff_apply(&stP[g], h) < h) keep = 0;
            if (keep) S1.a[w++] = S1.a[i];
        }
        S1.n = w;
    }
    n1kept = S1.n;
    if (S1.n == 0) return;
    cur = x;
    for (int i = D0; i < nv; i++) setbit(&cur, i, 0);
    dfs_collect(jD1, jD2, EV2, ev2_start, nodes2, &S2);
    *np2 = S2.n;
    if (S2.n == 0) return;
    if (use_stab && st_ns > 0) {
        MuEnt *me = malloc(sizeof(MuEnt) * S2.n);
        for (long long j = 0; j < S2.n; j++) {
            uint64_t h2 = h2part(S2.a[j]), m = ~0ULL;
            for (int g = 0; g < st_ns; g++) { uint64_t y = aff_apply(&stS[g], h2); if (y < m) m = y; }
            me[j].mu = m; me[j].a = S2.a[j];
        }
        qsort(me, S2.n, sizeof(MuEnt), cmp_mu_desc);
        mu2 = realloc(mu2, sizeof(uint64_t) * S2.n);
        for (long long j = 0; j < S2.n; j++) { mu2[j] = me[j].mu; S2.a[j] = me[j].a; }
        free(me);
    }
    /* block-2 parts without the separator bits, so that s1 | s2 = s1 ^ s2p */
    static u128 *s2p = NULL; static long long s2cap = 0;
    if (S2.n > s2cap) { s2cap = S2.n; s2p = realloc(s2p, sizeof(u128) * s2cap); }
    for (long long j = 0; j < S2.n; j++) { s2p[j].lo = S2.a[j].lo ^ x.lo; s2p[j].hi = S2.a[j].hi ^ x.hi; }
    /* order of the cross events: conditional greedy on a deterministic sample of pairs (the next event kills the most
     * sample pairs not killed by the earlier ones); events killing no remaining sample pair keep their natural order */
    int *ord = malloc(sizeof(int) * (n3 + 1)), nord = 0, KP = 0;
    long long NS = S1.n * S2.n >= 4096 ? 65536 : 0;
    if (NS > 0 && n3 > 0) {
        int nwd = (int)(NS / 64);
        uint64_t *K = calloc((size_t)n3 * nwd, 8), *alive = malloc(8 * nwd);
        for (long long t = 0; t < NS; t++) {
            long long i = (t * 7919) % S1.n, j = (t * 104729) % S2.n;
            u128 v; v.lo = S1.a[i].lo | S2.a[j].lo; v.hi = S1.a[i].hi | S2.a[j].hi;
            for (int q = 0; q < n3; q++)
                if (dead_after(&EV[ev3[q]], syndrome(&W[EV[ev3[q]].w], v))) K[(size_t)q * nwd + t / 64] |= 1ULL << (t % 64);
        }
        for (int t = 0; t < nwd; t++) alive[t] = ~0ULL;
        char *used = calloc(n3, 1);
        while (nord < n3) {
            int best = -1; long long bk = 0;
            for (int q = 0; q < n3; q++) {
                if (used[q]) continue;
                long long c = 0;
                for (int t = 0; t < nwd; t++) c += __builtin_popcountll(K[(size_t)q * nwd + t] & alive[t]);
                if (c > bk) { bk = c; best = q; }
            }
            if (best < 0) break;
            used[best] = 1; ord[nord++] = ev3[best];
            for (int t = 0; t < nwd; t++) alive[t] &= ~K[(size_t)best * nwd + t];
        }
        KP = nord < 32 ? nord : 32;
        while (KP > 0 && (double)KP * S2.n * 2 > 4.0e8) KP--;
        for (int q = 0; q < n3; q++) if (!used[q]) ord[nord++] = ev3[q];
        free(used); free(K); free(alive);
    } else {
        for (int q = 0; q < n3; q++) ord[nord++] = ev3[q];
    }
    /* prefilter on the first KP events: reduced syndrome = a[k] ^ Bv16[j*KP + k], where a = reduced row part (with
     * constant) and Bv16 = reduced block-2 part. The reduction modulo the event's fully reduced basis (pivot = lowest
     * set bit, no pivot bit in another basis vector) is linear, so the XOR of reduced parts is the reduced syndrome.
     * Survivors are checked against the remaining cross events directly. */
    uint16_t *Bv16 = KP ? malloc(sizeof(uint16_t) * KP * S2.n) : NULL;
    for (int k = 0; k < KP; k++) {
        const Event *ev = &EV[ord[k]];
        const Word *w = &W[ev->w];
        for (long long j = 0; j < S2.n; j++) {
            uint32_t sy = 0;
            for (int q = 0; q < w->m; q++) sy ^= (uint32_t)par128(w->A[q], s2p[j]) << q;
            Bv16[(size_t)j * KP + k] = (uint16_t)reduce_ev(ev, sy);
        }
    }
    uint32_t a[32];
    const uint8_t *dk[32];
    for (int k = 0; k < KP; k++) dk[k] = EV[ord[k]].dead;
    for (long long i = split_k; i < S1.n; i += split_n) {
        for (int k = 0; k < KP; k++) a[k] = reduce_ev(&EV[ord[k]], syndrome(&W[EV[ord[k]].w], S1.a[i]));
        long long jl = jlimit(hpart(S1.a[i]));
        for (long long j = 0; j < jl; j++) {
            (*npair)++;
            int ok = 1;
            const uint16_t *bj = Bv16 + (size_t)j * KP;
            for (int k = 0; k < KP; k++) {
                uint32_t v = a[k] ^ bj[k];
                if ((dk[k][v >> 3] >> (v & 7)) & 1) { ok = 0; break; }
            }
            if (!ok) continue;
            cur.lo = S1.a[i].lo | S2.a[j].lo; cur.hi = S1.a[i].hi | S2.a[j].hi;
            for (int q = KP; q < nord && ok; q++) {
                const Event *ev = &EV[ord[q]];
                if (dead_after(ev, syndrome(&W[ev->w], cur))) ok = 0;
            }
            if (!ok) continue;
            (*npass)++;
            if (dump_pairs) printf("PP %llx %llx\n", (unsigned long long)hpart(cur), (unsigned long long)h2part(cur));
            else {
                dfs(jD2);
                if (++npass_total % RESORT_EVERY == 0) resort_deep(jD2);
            }
        }
    }
    free(Bv16); free(ord);
}


/* ---------- xrepsfull: orbit representatives for a separator of ZB <= 40 bits with the whole group applied
 * directly (no second stage). For each z in increasing order not yet marked: mark all |G| images A_g(z) in a 2^ZB-bit
 * bitmap (malloc'ed in-process), count |Stab(z)| = #{g : A_g(z) = z}; keep z if it passes the checks at depth <= ZB. */
static void xrepsfull(const char *actfile, const char *outfile) {
    FILE *f = fopen(actfile, "rb");
    if (!f || fread(&ng_act, 4, 1, f) != 1 || fread(&nx_act, 4, 1, f) != 1) { fprintf(stderr, "act read\n"); exit(1); }
    act_rows = malloc(sizeof(uint64_t) * ng_act * nx_act);
    act_cst = malloc(sizeof(uint64_t) * ng_act);
    for (int g = 0; g < ng_act; g++)
        if ((int)fread(act_rows + (size_t)g * nx_act, 8, nx_act, f) != nx_act || fread(act_cst + g, 8, 1, f) != 1) exit(1);
    fclose(f);
    const int ZB = nx_act;
    if (ZB > 40) { fprintf(stderr, "ZB too large\n"); exit(1); }
    uint64_t nbits = 1ULL << ZB, nwords = nbits / 64 + 1;
    uint64_t *vis = malloc(nwords * 8);
    if (!vis) { fprintf(stderr, "bitmap malloc failed\n"); exit(1); }
    memset(vis, 0, nwords * 8);
    fprintf(stderr, "bitmap %.2f GiB allocated\n", nwords * 8.0 / (1ULL << 30));
    FILE *of = fopen(outfile, "w");
    long long norb = 0, nvalid = 0; double sumorb = 0;
    long long sh[64] = {0};
    /* columns: image(z) = c_g ^ XOR_{j in z} col[g][j] */
    uint64_t *col = malloc(sizeof(uint64_t) * ng_act * ZB);
    for (int g = 0; g < ng_act; g++)
        for (int j = 0; j < ZB; j++) {
            uint64_t c = 0;
            for (int i = 0; i < ZB; i++) if ((act_rows[(size_t)g * nx_act + i] >> j) & 1) c |= 1ULL << i;
            col[(size_t)g * ZB + j] = c;
        }
    uint64_t *buf = malloc(sizeof(uint64_t) * ng_act);
    int bits[64];
    for (uint64_t wi = 0; wi < nwords; wi++) {
        while (~vis[wi]) {
            int b = __builtin_ctzll(~vis[wi]);
            uint64_t z0 = wi * 64 + b;
            if (z0 >= nbits) goto done;
            int nb = 0;
            for (int j = 0; j < ZB; j++) if ((z0 >> j) & 1) bits[nb++] = j;
            int st = 0;
            for (int g = 0; g < ng_act; g++) {
                const uint64_t *cg = col + (size_t)g * ZB;
                uint64_t z = act_cst[g];
                for (int t = 0; t < nb; t++) z ^= cg[bits[t]];
                buf[g] = z;
                if (z == z0) st++;
            }
            for (int g = 0; g < ng_act; g++) {
                if (g + 16 < ng_act) __builtin_prefetch(&vis[buf[g + 16] >> 6], 1, 0);
                vis[buf[g] >> 6] |= 1ULL << (buf[g] & 63);
            }
            if (!((vis[wi] >> b) & 1)) { fprintf(stderr, "identity missing?\n"); exit(1); }
            norb++;
            cur.lo = z0; cur.hi = 0;
            if (check_prefix(ZB, cur)) {
                fprintf(of, "0 %llx\n", (unsigned long long)z0);
                nvalid++;
                sumorb += (double)ng_act / st;
                if (st < 64) sh[st]++;
            }
            if ((norb & ((1LL << 20) - 1)) == 0) { fprintf(stderr, "orbits %lld valid %lld z0 %llx\n", norb, nvalid, (unsigned long long)z0); }
        }
    }
done:
    fclose(of);
    printf("XREPSFULL orbits %lld valid %lld sum_orbit_sizes_valid %.0f\n", norb, nvalid, sumorb);
    printf("STABHIST");
    for (int i = 1; i < 64; i++) if (sh[i]) printf(" %d:%lld", i, sh[i]);
    printf("\n");
}


/* ---------- joinq: work-queue driver for the join mode (dynamic load balancing, resumable).
 * QDIR/queue/<chunk> files hold prefix lines "0 x". A worker claims a chunk by rename() to QDIR/running/<chunk>.<id>
 * (atomic; smallest names first), runs join on every line, writes QDIR/out/<chunk>.tmp, renames it to
 * QDIR/out/<chunk>.out, then renames the running file to QDIR/done/<chunk>. Stops when the queue is empty. */
#include <dirent.h>
#include <errno.h>
static int cmpstr(const void *a, const void *b) { return strcmp(*(const char * const *)a, *(const char * const *)b); }
static void joinq(const char *qdir, int D0, int D1, int D2, int wid) {
    char path[4096], path2[4096];
    join_setup(D0, D1, D2);
    long long nchunks = 0;
    while (1) {
        snprintf(path, sizeof path, "%s/queue", qdir);
        DIR *dp = opendir(path);
        if (!dp) { fprintf(stderr, "no queue dir\n"); exit(1); }
        char **names = NULL; int nn = 0, cap = 0;
        struct dirent *de;
        while ((de = readdir(dp))) {
            if (de->d_name[0] == '.') continue;
            if (nn == cap) { cap = cap ? 2 * cap : 4096; names = realloc(names, sizeof(char *) * cap); }
            names[nn++] = strdup(de->d_name);
        }
        closedir(dp);
        if (nn == 0) { free(names); break; }
        qsort(names, nn, sizeof(char *), cmpstr);
        int got = -1;
        for (int t = 0; t < nn && got < 0; t++) {
            snprintf(path, sizeof path, "%s/queue/%s", qdir, names[t]);
            snprintf(path2, sizeof path2, "%s/running/%s.%d", qdir, names[t], wid);
            if (rename(path, path2) == 0) got = t;
        }
        if (got < 0) { for (int t = 0; t < nn; t++) free(names[t]); free(names); continue; }
        char chunk[1024]; snprintf(chunk, sizeof chunk, "%s", names[got]);
        for (int t = 0; t < nn; t++) free(names[t]);
        free(names);
        FILE *pf = fopen(path2, "r");
        snprintf(path, sizeof path, "%s/out/%s.tmp", qdir, chunk);
        FILE *of = fopen(path, "w");
        if (!pf || !of) { fprintf(stderr, "chunk io error\n"); exit(1); }
        unsigned long long hi, lo;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            if (hi) { fprintf(stderr, "nonzero hi word\n"); exit(1); }
            u128 xx; xx.hi = 0; xx.lo = lo;
            long long b1 = 0, b2 = 0, sb = nsol;
            for (int d = 0; d <= nv; d++) { b1 += nodes[d]; b2 += nodes2[d]; }
            int ok = check_prefix(D0, xx);
            long long np1 = 0, np2 = 0, npair = 0, npass = 0;
            FILE *saved = stdout; stdout = of;          /* SOL lines of this chunk go to its output file */
            if (ok) join_one(xx, D0, &np1, &np2, &npair, &npass);
            stdout = saved;
            long long a1 = 0, a2 = 0;
            for (int d = 0; d <= nv; d++) { a1 += nodes[d]; a2 += nodes2[d]; }
            fprintf(of, "J %llx %d %lld %lld %lld %lld %lld %lld %lld\n", lo, ok, np1, np2, npair, npass, a1 - b1, a2 - b2, nsol - sb);
            fflush(of);     /* engine14: each finished rep is visible at once (shows which rep a long chunk is on) */
        }
        fclose(pf);
        fclose(of);
        snprintf(path2, sizeof path2, "%s/out/%s.out", qdir, chunk);
        if (rename(path, path2) != 0) { fprintf(stderr, "rename out failed\n"); exit(1); }
        snprintf(path, sizeof path, "%s/running/%s.%d", qdir, chunk, wid);
        snprintf(path2, sizeof path2, "%s/done/%s", qdir, chunk);
        if (rename(path, path2) != 0) { fprintf(stderr, "rename done failed\n"); exit(1); }
        nchunks++;
    }
    fprintf(stderr, "worker %d finished %lld chunks\n", wid, nchunks);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
    load(argv[1]);
    const char *mode = argv[2];
    clock_t t0 = clock();
    dmax = nv;
    if (!strcmp(mode, "full")) {
        cur.lo = cur.hi = 0;
        if (check_depth(0, cur)) dfs(0);
    } else if (!strcmp(mode, "prefixes")) {
        FILE *pf = fopen(argv[3], "r");
        int D = atoi(argv[4]);
        long long NCH = argc > 6 ? atoll(argv[5]) : 1, CH = argc > 6 ? atoll(argv[6]) : 0;
        if (argc > 7) dmax = atoi(argv[7]);   /* optional depth cap: nodes at depth dmax are counted as leaves */
        unsigned long long hi, lo;
        long long np = 0, npass = 0, line = -1;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            line++;
            if (line % NCH != CH) continue;
            if (hi) { fprintf(stderr, "nonzero hi word\n"); exit(1); }
            np++;
            cur.hi = hi; cur.lo = lo;
            long long before = 0; for (int d = 0; d <= nv; d++) before += nodes[d];
            long long sb = nsol;
            int ok = check_prefix(D, cur);
            if (ok) { npass++; dfs(D); }
            long long after = 0; for (int d = 0; d <= nv; d++) after += nodes[d];
            printf("P %llx %d %lld %lld\n", lo, ok, after - before, nsol - sb);
            fflush(stdout);
        }
        fclose(pf);
        fprintf(stderr, "prefixes %lld passing %lld\n", np, npass);
    } else if (!strcmp(mode, "joinq")) {
        joinq(argv[3], atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]));
    } else if (!strcmp(mode, "join")) {
        /* join FILE D0 D1 D2 [NCH CH] */
        FILE *pf = fopen(argv[3], "r");
        int D0 = atoi(argv[4]), D1 = atoi(argv[5]), D2 = atoi(argv[6]);
        long long NCH = argc > 8 ? atoll(argv[7]) : 1, CH = argc > 8 ? atoll(argv[8]) : 0, line = -1;
        join_setup(D0, D1, D2);
        unsigned long long hi, lo;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            line++;
            if (line % NCH != CH) continue;
            if (hi) { fprintf(stderr, "nonzero hi word\n"); exit(1); }
            u128 x; x.hi = 0; x.lo = lo;
            long long b1 = 0, b2 = 0, b3 = 0, sb = nsol;
            for (int d = 0; d <= nv; d++) { b1 += nodes[d]; b2 += nodes2[d]; }
            int ok = check_prefix(D0, x);
            long long np1 = 0, np2 = 0, npair = 0, npass = 0;
            if (ok) join_one(x, D0, &np1, &np2, &npair, &npass);
            long long a1 = 0, a2 = 0;
            for (int d = 0; d <= nv; d++) { a1 += nodes[d]; a2 += nodes2[d]; }
            (void)b3;
            printf("J %llx %d %lld %lld %lld %lld %lld %lld %lld\n", lo, ok, np1, np2, npair, npass, a1 - b1, a2 - b2, nsol - sb);
            fflush(stdout);
        }
        fclose(pf);
    } else if (!strcmp(mode, "joinsplit")) {
        /* joinsplit FILE D0 D1 D2 NSPLIT SPLIT: join on every line of FILE, the pair phase restricted to the rows
         * i % NSPLIT == SPLIT of S1. Output per line:
         * JS x ok |S1| |S2| npair npass nodes_phase1 nodes_pairs nodes2 nsol NSPLIT SPLIT
         * Over SPLIT = 0..NSPLIT-1 the pairs are partitioned, so the J line of plain join is
         * J x ok |S1| |S2| sum(npair) sum(npass) nodes_phase1 + sum(nodes_pairs) nodes2 sum(nsol). */
        FILE *pf = fopen(argv[3], "r");
        int D0 = atoi(argv[4]), D1 = atoi(argv[5]), D2 = atoi(argv[6]);
        if (argc < 9) { fprintf(stderr, "joinsplit FILE D0 D1 D2 NSPLIT SPLIT\n"); exit(1); }
        split_n = atoll(argv[7]); split_k = atoll(argv[8]);
        if (split_n < 1 || split_k < 0 || split_k >= split_n) { fprintf(stderr, "bad split\n"); exit(1); }
        join_setup(D0, D1, D2);
        unsigned long long hi, lo;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            if (hi) { fprintf(stderr, "nonzero hi word\n"); exit(1); }
            u128 x; x.hi = 0; x.lo = lo;
            long long b1 = nodes_sum(), b2 = 0, sb = nsol;
            for (int d = 0; d <= nv; d++) b2 += nodes2[d];
            p1_mark = b1;
            int ok = check_prefix(D0, x);
            long long np1 = 0, np2 = 0, npair = 0, npass = 0;
            if (ok) join_one(x, D0, &np1, &np2, &npair, &npass);
            long long a1 = nodes_sum(), a2 = 0;
            for (int d = 0; d <= nv; d++) a2 += nodes2[d];
            printf("JS %llx %d %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld\n", lo, ok, np1, np2, npair, npass,
                   p1_mark - b1, a1 - p1_mark, a2 - b2, nsol - sb, split_n, split_k);
            fflush(stdout);
        }
        fclose(pf);
    } else if (!strcmp(mode, "joinstab") || !strcmp(mode, "joinstabdump")) {
        /* joinstab FILE D0 D1 D2 STABFILE NSPLIT SPLIT: joinsplit with the Stab(X) reduction (STABFILE "-" = none).
         * Output per line: JT x ok |S1| |S1 kept| |S2| npair npass nodes_phase1 nodes_pairs nodes2 nsol NSPLIT SPLIT nh ns
         * joinstabdump: same, but the passing pairs are printed (PP h h') instead of searched below D2. */
        if (argc < 10) { fprintf(stderr, "joinstab FILE D0 D1 D2 STABFILE NSPLIT SPLIT\n"); exit(1); }
        FILE *pf = fopen(argv[3], "r");
        int D0 = atoi(argv[4]), D1 = atoi(argv[5]), D2 = atoi(argv[6]);
        use_stab = strcmp(argv[7], "-") != 0;
        if (use_stab && (D0 != 36 || D1 != 70 || D2 != 104)) { fprintf(stderr, "joinstab with maps assumes blocks 36/70/104\n"); exit(1); }
        evkill = calloc(ne + 1, sizeof(long long));
        if (use_stab) load_stab(argv[7]);
        dump_pairs = !strcmp(mode, "joinstabdump");
        split_n = atoll(argv[8]); split_k = atoll(argv[9]);
        if (split_n < 1 || split_k < 0 || split_k >= split_n) { fprintf(stderr, "bad split\n"); exit(1); }
        join_setup(D0, D1, D2);
        unsigned long long hi, lo;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            if (hi) { fprintf(stderr, "nonzero hi word\n"); exit(1); }
            u128 x; x.hi = 0; x.lo = lo;
            if (use_stab) select_stab(lo); else { st_nh = 0; st_ns = 0; }
            long long b1 = nodes_sum(), b2 = 0, sb = nsol;
            for (int d = 0; d <= nv; d++) b2 += nodes2[d];
            p1_mark = b1; n1kept = 0;
            int ok = check_prefix(D0, x);
            long long np1 = 0, np2 = 0, npair = 0, npass = 0;
            if (ok) join_one(x, D0, &np1, &np2, &npair, &npass);
            long long a1 = nodes_sum(), a2 = 0;
            for (int d = 0; d <= nv; d++) a2 += nodes2[d];
            printf("JT %llx %d %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %d %d\n", lo, ok, np1, n1kept, np2,
                   npair, npass, p1_mark - b1, a1 - p1_mark, a2 - b2, nsol - sb, split_n, split_k, st_nh, st_ns);
            fflush(stdout);
        }
        fclose(pf);
    } else if (!strcmp(mode, "xrepsfull")) {
        xrepsfull(argv[3], argv[4]);
    } else if (!strcmp(mode, "canon")) {
        canon(argv[3], argv[4], argv[5], argv[6]);
    } else if (!strcmp(mode, "xreps")) {
        xreps(argv[3], argv[4], argv[5], argc > 6 ? atoi(argv[6]) : 30, argc > 7 ? atoi(argv[7]) : 10);
    } else if (!strcmp(mode, "feas")) {
        /* feas PREFIXFILE D DMAX MASKFILE|- : for each prefix, is depth DMAX reachable using only active words? */
        FILE *pf = fopen(argv[3], "r");
        int D = atoi(argv[4]);
        dmax = atoi(argv[5]);
        stop_first = 1;
        if (strcmp(argv[6], "-")) {
            active = calloc(nw, 1);
            FILE *mf = fopen(argv[6], "r");
            int wi;
            while (fscanf(mf, "%d", &wi) == 1) if (wi >= 0 && wi < nw) active[wi] = 1;
            fclose(mf);
            apply_mask();
        }
        unsigned long long hi, lo;
        long long NCH = argc > 8 ? atoll(argv[7]) : 1, CH = argc > 8 ? atoll(argv[8]) : 0, line = -1, nfp = 0;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            line++;
            if (line % NCH != CH) continue;
            if (hi) { fprintf(stderr, "nonzero hi word\n"); exit(1); }
            nfp++;
            cur.hi = hi; cur.lo = lo;
            long long before = 0; for (int d = 0; d <= nv; d++) before += nodes[d];
            found = 0;
            if (check_prefix(D, cur)) dfs(D);
            long long after = 0; for (int d = 0; d <= nv; d++) after += nodes[d];
            printf("F %llx %d %lld\n", lo, found, after - before);
        }
        fclose(pf);
    } else if (!strcmp(mode, "knuth") || !strcmp(mode, "knuthpre")) {
        int knpre = !strcmp(mode, "knuthpre");
        int D = 0; long nprobe; FILE *pf = NULL;
        if (knpre) { pf = fopen(argv[3], "r"); D = atoi(argv[4]); nprobe = atol(argv[5]); rng_state = strtoull(argv[6], 0, 10) | 1; }
        else { nprobe = atol(argv[3]); rng_state = strtoull(argv[4], 0, 10) | 1; }
        double tot = 0; long npre = 0;
        unsigned long long hi, lo;
        while (1) {
            if (knpre) { if (fscanf(pf, "%llx %llx", &hi, &lo) != 2) break; cur.hi = hi; cur.lo = lo; if (!check_prefix(D, cur)) continue; }
            else { cur.lo = cur.hi = 0; if (npre) break; if (!check_depth(0, cur)) break; }
            npre++;
            double s = 0;
            for (long p = 0; p < nprobe; p++) s += knuth_probe(D);
            tot += s / nprobe;
        }
        for (int d = 0; d <= nv; d++) est[d] /= (double)nprobe;
        printf("KNUTH prefixes %ld mean_subtree %.6g total %.6g\n", npre, npre ? tot / npre : 0, tot);
        for (int d = 0; d <= nv; d++) if (est[d] > 0) printf("est depth %d %.6g\n", d, est[d]);
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    long long tot = 0;
    for (int d = 0; d <= nv; d++) tot += nodes[d];
    printf("DONE nodes %lld solutions %lld cpu %.2f\n", tot, nsol, secs);
    if (!strcmp(mode, "full") || !strcmp(mode, "prefixes") || !strcmp(mode, "join"))
        for (int d = 0; d <= nv; d++) if (nodes[d]) printf("nodes depth %d %lld\n", d, nodes[d]);
    if (!strcmp(mode, "join"))
        for (int d = 0; d <= nv; d++) if (nodes2[d]) printf("nodes2 depth %d %lld\n", d, nodes2[d]);
    return 0;
}
