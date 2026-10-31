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
    for (int b = 0; b < 2; b++) {
        setbit(&cur, d, b);
        if (check_depth(d + 1, cur)) dfs(d + 1);
        if (stop_first && found) break;
    }
    setbit(&cur, d, 0);
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
            fprintf(of, "%016llx %016llx %d %d\n", 0ULL, (unsigned long long)x, sx, osize * cls);
            nxrep++;
            sum_valid_orbit += (double)ng_act / sx;
        }
    }
    fclose(of);
    printf("XREPS zorbits %lld zvalid %lld xcand %lld xreps %lld sum_orbit_sizes %.0f\n", norb, nzvalid, nxcand, nxrep, sum_valid_orbit);
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
        unsigned long long hi, lo;
        long long np = 0, npass = 0;
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            np++;
            cur.hi = hi; cur.lo = lo;
            long long before = 0; for (int d = 0; d <= nv; d++) before += nodes[d];
            long long sb = nsol;
            int ok = check_prefix(D, cur);
            if (ok) { npass++; dfs(D); }
            long long after = 0; for (int d = 0; d <= nv; d++) after += nodes[d];
            printf("PX %016llx %016llx %d %lld %lld\n", hi, lo, ok, after - before, nsol - sb);
            fflush(stdout);
        }
        fclose(pf);
        fprintf(stderr, "prefixes %lld passing %lld\n", np, npass);
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
        while (fscanf(pf, "%llx %llx", &hi, &lo) == 2) {
            cur.hi = hi; cur.lo = lo;
            long long before = 0; for (int d = 0; d <= nv; d++) before += nodes[d];
            found = 0;
            if (check_prefix(D, cur)) dfs(D);
            long long after = 0; for (int d = 0; d <= nv; d++) after += nodes[d];
            printf("FEAS %016llx %016llx %d %lld\n", hi, lo, found, after - before);
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
    if (!strcmp(mode, "full") || !strcmp(mode, "prefixes"))
        for (int d = 0; d <= nv; d++) if (nodes[d]) printf("nodes depth %d %lld\n", d, nodes[d]);
    return 0;
}
