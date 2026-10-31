// Guess-and-determine solver for the C2 x C2 instances (free bits <= 64), optimised version.
// Words: d affine class forms (mask . w + c), good set G in F2^d.  Residual forms are kept reduced modulo the
// chosen equations (each new equation's pivot = its lowest set bit; it is XORed into every form with that bit).
// Per-word cache (rank, relations, option count) is recomputed only for words whose forms changed.
// Modes: search (exhaustive, optional hash split at a depth) or knuth (random probes) with heuristic H.
// Usage: v4gd2 INSTANCE WMAX MODE(search|knuth) HEUR SPLITDEPTH NPART PART PROBES_OR_NODELIMIT SEED
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef uint64_t u64;
static int NW, NWORDS, NPROP, NF, NF_ALL;
static int *wwt, *wd, *woff, *wngood; static u64 **wgood; static int16_t **wwht;
static u64 *fmask, *fmask0; static unsigned char *fval, *fval0; static int *fword;
static int *ustack; static long usp, ucap;
static u64 eqmask[64]; static unsigned char eqval[64]; static int neq;
// cache
static unsigned char *wvalid; static int *wrank, *wnrel, *wcount; static int (*wrelm)[12]; static unsigned char (*wrelp)[12];
static int *dlist; static int ndl; static unsigned char *indl;
static u64 (*wbas)[12]; static int *wnb;                // echelon basis of residual span, pivots = lowest bits
static int *blog_w; static unsigned char *blog_s; static u64 *blog_v; static long blp, blcap;   // basis undo log
static long *eq_blp;                                     // log position at each equation
static long long nodes = 0, sols = 0, nodelimit = 0, hist[80];
static int HEUR, SPLIT = -1, NPART = 1, PART = 0; static long long splitcount = 0;
static time_t tstart;
static void die(const char *m) { fprintf(stderr, "%s\n", m); exit(1); }
static unsigned long long rng_state = 88172645463325252ULL;
static inline u64 rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static void read_instance(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open");
    if (fscanf(f, "%d %d", &NW, &NWORDS) != 2) die("hdr");
    wwt = malloc(sizeof(int) * NWORDS); wd = malloc(sizeof(int) * NWORDS); woff = malloc(sizeof(int) * NWORDS);
    wngood = malloc(sizeof(int) * NWORDS); wgood = malloc(sizeof(u64 *) * NWORDS); wwht = malloc(sizeof(int16_t *) * NWORDS);
    int cap = 1 << 20; fmask = malloc(sizeof(u64) * cap); fval = malloc(cap); fword = malloc(sizeof(int) * cap); NF = 0;
    for (int i = 0; i < NWORDS; i++) {
        int wt, d, ng; if (fscanf(f, "%d %d %d", &wt, &d, &ng) != 3) die("word");
        if (d > 12) die("d>12");
        wwt[i] = wt; wd[i] = d; woff[i] = NF; wngood[i] = ng;
        for (int t = 0; t < d; t++) {
            unsigned long long m; int c; if (fscanf(f, "%llx %d", &m, &c) != 2) die("form");
            fmask[NF] = m; fval[NF] = c; fword[NF] = i; NF++;
        }
        int nb = ((1 << d) + 63) / 64; wgood[i] = calloc(nb, sizeof(u64));
        for (int k = 0; k < ng; k++) { int g; if (fscanf(f, "%d", &g) != 1) die("good"); wgood[i][g >> 6] |= 1ULL << (g & 63); }
        int n = 1 << d; int *a = malloc(sizeof(int) * n);
        for (int g = 0; g < n; g++) a[g] = (wgood[i][g >> 6] >> (g & 63)) & 1;
        for (int h = 1; h < n; h <<= 1) for (int s = 0; s < n; s += 2 * h) for (int j = s; j < s + h; j++) { int x = a[j], y = a[j + h]; a[j] = x + y; a[j + h] = x - y; }
        wwht[i] = malloc(sizeof(int16_t) * n); for (int g = 0; g < n; g++) wwht[i][g] = (int16_t)a[g]; free(a);
    }
    fclose(f);
}
static inline int good(int w, int g) { return (wgood[w][g >> 6] >> (g & 63)) & 1; }

// solve relation system: relations r_k (mask over class bits, parity) -> enumerate consistent classes
static int enum_classes(int w, int *out, int maxout) {
    int d = wd[w], r = wnrel[w]; int *relm = wrelm[w]; unsigned char *relp = wrelp[w];
    // reduce relations to echelon form over class bits: pivot = highest bit
    int R[12], Pp[12], P[12], nr = 0;
    for (int k = 0; k < r; k++) {
        int m = relm[k], p = relp[k];
        for (int j = 0; j < nr; j++) if ((m >> P[j]) & 1) { m ^= R[j]; p ^= Pp[j]; }
        if (!m) { if (p) return 0; continue; }
        int pb = 31 - __builtin_clz(m);
        for (int j = 0; j < nr; j++) if ((R[j] >> pb) & 1) { R[j] ^= m; Pp[j] ^= p; }
        R[nr] = m; Pp[nr] = p; P[nr] = pb; nr++;
    }
    int pivmask = 0; for (int j = 0; j < nr; j++) pivmask |= 1 << P[j];
    int fb[12], nf = 0; for (int t = 0; t < d; t++) if (!((pivmask >> t) & 1)) fb[nf++] = t;
    int c = 0;
    for (int x = 0; x < (1 << nf); x++) {
        int g = 0; for (int i = 0; i < nf; i++) if ((x >> i) & 1) g |= 1 << fb[i];
        for (int j = 0; j < nr; j++) { int par = Pp[j] ^ (__builtin_popcount(R[j] & g & ~(1 << P[j])) & 1); if (par) g |= 1 << P[j]; }
        if (good(w, g)) { if (out && c < maxout) out[c] = g; c++; }
    }
    return c;
}
static void recompute(int w) {
    int d = wd[w], off = woff[w], nb = 0, r = 0; u64 bvec[12]; int bcomb[12];
    for (int t = 0; t < d; t++) {
        u64 v = fmask[off + t]; int comb = 1 << t;
        for (int k = 0; k < nb; k++) if (v & (bvec[k] & -bvec[k])) { v ^= bvec[k]; comb ^= bcomb[k]; }
        if (!v) { int p = 0; for (int s = 0; s < d; s++) if ((comb >> s) & 1) p ^= fval[off + s]; wrelm[w][r] = comb; wrelp[w][r] = p; r++; }
        else { bvec[nb] = v; bcomb[nb] = comb; nb++; }
    }
    wrank[w] = nb; wnrel[w] = r;
    if (r == 0) wcount[w] = wngood[w];
    else if (r <= d - r) {
        long s = 0;
        for (int x = 0; x < (1 << r); x++) {
            int m = 0, p = 0; for (int k = 0; k < r; k++) if ((x >> k) & 1) { m ^= wrelm[w][k]; p ^= wrelp[w][k]; }
            int v = wwht[w][m]; s += p ? -v : v;
        }
        wcount[w] = (int)(s >> r);
    } else wcount[w] = enum_classes(w, NULL, 0);
    wvalid[w] = 1;
}
static inline void mark(int w) { wvalid[w] = 0; if (!indl[w]) { indl[w] = 1; dlist[ndl++] = w; } }
static inline void blog_push(int w, int s, u64 v) {
    if (blp >= blcap) { blcap *= 2; blog_w = realloc(blog_w, sizeof(int) * blcap); blog_s = realloc(blog_s, blcap); blog_v = realloc(blog_v, sizeof(u64) * blcap); }
    blog_w[blp] = w; blog_s[blp] = (unsigned char)s; blog_v[blp] = v; blp++;
}
static void add_eq(u64 l, int e) {
    u64 b = l & -l; eq_blp[neq] = blp; eqmask[neq] = l; eqval[neq] = e; neq++;
    long start = usp;
    for (int i = 0; i < NF; i++) if (fmask[i] & b) {
        fmask[i] ^= l; fval[i] ^= e;
        if (usp + 2 >= ucap) { ucap *= 2; ustack = realloc(ustack, sizeof(int) * ucap); }
        ustack[usp++] = i;
    }
    ustack[usp++] = (int)(usp - start);
    // bases
    for (int w = 0; w < NPROP; w++) {
        int nb = wnb[w]; u64 *B = wbas[w]; int sp = -1;
        for (int k = 0; k < nb; k++) {
            u64 v = B[k];
            if (!(v & b)) continue;
            blog_push(w, k, v);
            if ((v & -v) == b) sp = k;
            B[k] = v ^ l;
        }
        if (sp >= 0) {
            // reduce B[sp] (its pivot changed) against the other vectors by lowest-bit pivots
            u64 x = B[sp];
            for (;;) {
                if (!x) break;
                u64 lb = x & -x; int hit = -1;
                for (int k = 0; k < nb; k++) if (k != sp && (B[k] & -B[k]) == lb) { hit = k; break; }
                if (hit < 0) break;
                x ^= B[hit];
            }
            if (!x) {
                // rank drop: remove slot sp (swap with last)
                if (sp != nb - 1) { blog_push(w, nb - 1, B[nb - 1]); B[sp] = B[nb - 1]; }
                blog_push(w, 100 + nb, 0);          // marker: nb was nb (restore count)
                wnb[w] = nb - 1; mark(w);
            } else B[sp] = x;
        }
    }
}
static void undo_eq(void) {
    neq--; u64 l = eqmask[neq]; int e = eqval[neq]; int cnt = ustack[--usp];
    for (int k = 0; k < cnt; k++) { int i = ustack[--usp]; fmask[i] ^= l; fval[i] ^= e; }
    long to = eq_blp[neq];
    while (blp > to) {
        blp--; int w = blog_w[blp], s = blog_s[blp];
        if (s >= 100) { wnb[w] = s - 100; mark(w); }
        else wbas[w][s] = blog_v[blp];
    }
}
static int apply_class(int w, int g) {
    int d = wd[w], off = woff[w], added = 0;
    for (int t = 0; t < d; t++) {
        u64 m = fmask[off + t]; int want = ((g >> t) & 1) ^ fval[off + t];
        if (!m) { if (want) { for (int k = 0; k < added; k++) undo_eq(); return -1; } continue; }
        add_eq(m, want); added++;
    }
    return added;
}
// propagation over dirty words; returns 0 on conflict; sets *nadded
static int propagate(int *nadded) {
    *nadded = 0;
    while (ndl > 0) {
        int w = dlist[--ndl]; indl[w] = 0;
        if (w >= NPROP) continue;
        recompute(w);
        if (wcount[w] == 0) { // flush dirty list
            while (ndl > 0) { int x = dlist[--ndl]; indl[x] = 0; }
            return 0;
        }
        if (wcount[w] == 1 && wrank[w] > 0) {
            int g; enum_classes(w, &g, 1);
            int a = apply_class(w, g);
            if (a < 0) { while (ndl > 0) { int x = dlist[--ndl]; indl[x] = 0; } return 0; }
            *nadded += a;
        }
    }
    return 1;
}
static int choose(void) {
    int best = -1; double bs = 1e300;
    for (int w = 0; w < NPROP; w++) {
        if (!wvalid[w]) recompute(w);
        if (wrank[w] == 0) continue;
        double s;
        if (HEUR == 0) s = wcount[w];
        else if (HEUR == 1) s = log2((double)wcount[w]) / wrank[w] - 1.0;        // bits per fixed dimension
        else s = (double)wcount[w] / (double)(1 << wrank[w]);                    // fraction kept
        if (s < bs) { bs = s; best = w; }
    }
    return best;
}
static int NWORDS_ALL;
static int check_leaf(void) {
    u64 RL[64], P[64]; int RE[64], nr = 0; u64 piv = 0;
    for (int k = 0; k < neq; k++) {
        u64 l = eqmask[k]; int e = eqval[k];
        for (int j = 0; j < nr; j++) if (l & P[j]) { l ^= RL[j]; e ^= RE[j]; }
        if (!l) { if (e) return 0; continue; }
        u64 b = l & -l; for (int j = 0; j < nr; j++) if (RL[j] & b) { RL[j] ^= l; RE[j] ^= e; }
        P[nr] = b; RL[nr] = l; RE[nr] = e; nr++; piv |= b;
    }
    u64 all = NW == 64 ? ~0ULL : ((1ULL << NW) - 1); u64 freeb = all & ~piv; int nf = __builtin_popcountll(freeb);
    if (nf > 26) { printf("LEAF free %d not enumerated\n", nf); fflush(stdout); return 1; }
    int fb[64], k2 = 0; for (int i = 0; i < NW; i++) if ((freeb >> i) & 1) fb[k2++] = i;
    int found = 0;
    for (long x = 0; x < (1L << nf); x++) {
        u64 w = 0; for (int i = 0; i < nf; i++) if ((x >> i) & 1) w |= 1ULL << fb[i];
        for (int j = 0; j < nr; j++) if (RE[j] ^ (__builtin_popcountll((RL[j] & ~P[j]) & w) & 1)) w |= P[j];
        int ok = 1;
        for (int q = 0; q < NWORDS_ALL && ok; q++) {
            int d = wd[q], off = woff[q], g = 0;
            for (int t = 0; t < d; t++) g |= ((__builtin_popcountll(fmask0[off + t] & w) & 1) ^ fval0[off + t]) << t;
            if (!good(q, g)) ok = 0;
        }
        if (ok) { found++; printf("SOLUTION w=%016llx\n", (unsigned long long)w); fflush(stdout); }
    }
    return found > 0;
}
static int search(int depth) {
    nodes++; if (depth < 80) hist[depth]++;
    if (nodelimit && nodes > nodelimit) return 2;
    if ((nodes & 0xFFFFF) == 0) { fprintf(stderr, "nodes %lld depth %d neq %d t=%lds\n", nodes, depth, neq, (long)(time(NULL) - tstart)); }
    int nadded, ret = 0;
    if (propagate(&nadded)) {
        int bw = choose();
        if (bw < 0) { if (check_leaf()) { sols++; } }
        else {
            int skip = 0;
            if (depth == SPLIT) { long long id = splitcount++; if (id % NPART != PART) skip = 1; }
            if (!skip) {
                int opts[4096]; int no = enum_classes(bw, opts, 4096);
                for (int k = 0; k < no && ret != 2; k++) {
                    int a = apply_class(bw, opts[k]); if (a < 0) continue;
                    int r = search(depth + 1);
                    for (int q = 0; q < a; q++) undo_eq();
                    if (r == 2) ret = 2;
                }
            }
        }
    }
    for (int k = 0; k < nadded; k++) undo_eq();
    // after undo, propagate dirtiness is handled lazily (wvalid=0)
    while (ndl > 0) { int x = dlist[--ndl]; indl[x] = 0; }
    return ret;
}
static void knuth(long probes) {
    double est[80] = {0}; long ends[80] = {0};
    for (long p = 0; p < probes; p++) {
        double wgt = 1.0; int depth = 0; int stack = 0;
        for (;;) {
            if (depth < 80) est[depth] += wgt;
            int nadded; int ok = propagate(&nadded); stack += nadded;
            if (!ok) { ends[depth]++; break; }
            int bw = choose();
            if (bw < 0) { ends[depth]++; printf("probe reached a leaf at depth %d\n", depth); break; }
            int opts[4096]; int no = enum_classes(bw, opts, 4096);
            int g = opts[rnd() % no]; wgt *= no;
            int a = apply_class(bw, g); if (a < 0) { ends[depth]++; break; }
            stack += a; depth++;
        }
        for (int k = 0; k < stack; k++) undo_eq();
        while (ndl > 0) { int x = dlist[--ndl]; indl[x] = 0; }
        for (int w = 0; w < NPROP; w++) wvalid[w] = 0;
    }
    double tot = 0; printf("Knuth estimate (%ld probes, heur %d):", probes, HEUR);
    for (int d = 0; d < 80; d++) if (est[d] > 0) { printf(" %d:%.2e", d, est[d] / probes); tot += est[d] / probes; }
    printf("\nTOTAL %.3e  ends:", tot); for (int d = 0; d < 80; d++) if (ends[d]) printf(" %d:%ld", d, ends[d]); printf("\n");
}
int main(int argc, char **argv) {
    if (argc < 10) die("usage: v4gd2 INSTANCE WMAX MODE HEUR SPLITDEPTH NPART PART PROBES_OR_NODELIMIT SEED");
    read_instance(argv[1]); int wmax = atoi(argv[2]); const char *mode = argv[3]; HEUR = atoi(argv[4]);
    SPLIT = atoi(argv[5]); NPART = atoi(argv[6]); PART = atoi(argv[7]); long long lim = atoll(argv[8]); rng_state ^= (u64)atoll(argv[9]) * 0x9E3779B97F4A7C15ULL;
    NPROP = 0; while (NPROP < NWORDS && wwt[NPROP] <= wmax) NPROP++;
    NWORDS_ALL = NWORDS; NF_ALL = NF;
    fmask0 = malloc(sizeof(u64) * NF); fval0 = malloc(NF); memcpy(fmask0, fmask, sizeof(u64) * NF); memcpy(fval0, fval, NF);
    NF = NPROP < NWORDS ? woff[NPROP] : NF;
    ucap = 1 << 22; ustack = malloc(sizeof(int) * ucap); usp = 0;
    wvalid = calloc(NWORDS, 1); wrank = calloc(NWORDS, sizeof(int)); wnrel = calloc(NWORDS, sizeof(int)); wcount = calloc(NWORDS, sizeof(int));
    wrelm = calloc(NWORDS, sizeof(*wrelm)); wrelp = calloc(NWORDS, sizeof(*wrelp)); dlist = malloc(sizeof(int) * NWORDS); indl = calloc(NWORDS, 1); ndl = 0;
    wbas = calloc(NWORDS, sizeof(*wbas)); wnb = calloc(NWORDS, sizeof(int));
    blcap = 1 << 22; blog_w = malloc(sizeof(int) * blcap); blog_s = malloc(blcap); blog_v = malloc(sizeof(u64) * blcap); blp = 0;
    eq_blp = malloc(sizeof(long) * 70);
    for (int w = 0; w < NPROP; w++) {
        int nb = 0; u64 *B = wbas[w];
        for (int t = 0; t < wd[w]; t++) {
            u64 x = fmask[woff[w] + t];
            for (;;) { if (!x) break; u64 lb = x & -x; int hit = -1; for (int k = 0; k < nb; k++) if ((B[k] & -B[k]) == lb) { hit = k; break; } if (hit < 0) break; x ^= B[hit]; }
            if (x) B[nb++] = x;
        }
        wnb[w] = nb;
    }
    for (int w = 0; w < NPROP; w++) { indl[w] = 1; dlist[ndl++] = w; }
    tstart = time(NULL);
    fprintf(stderr, "NW %d words %d prop %d forms %d\n", NW, NWORDS, NPROP, NF);
    if (!strcmp(mode, "knuth")) { knuth(lim); return 0; }
    nodelimit = lim;
    int r = search(0);
    printf("DONE result=%s nodes %lld sols %lld time %lds split=%d part %d/%d\nhist:", r == 2 ? "NODELIMIT" : "COMPLETE", nodes, sols, (long)(time(NULL) - tstart), SPLIT, PART, NPART);
    for (int i = 0; i < 80; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
    printf("\n"); return 0;
}
