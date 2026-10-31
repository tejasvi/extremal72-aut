/* lab.c -- independent Golay-labelling solver (C3 audit).  Point placement over bijections pi: reference Golay
   points -> E coordinates, normal form (verified by m24check.c): pi(p_i) = c_i (i=1..5, p1..p8 = points of the
   reference octad O0, c1..c5 a fixed 5-set), pi(p6) < pi(p7), pi(p6) < pi(p8), pi(q1) = min free coordinate.
   Forward checking on octads only (a candidate is removed only if an octad with 7 placed points would get a
   forbidden image); dodecads are checked at complete assignments.  Every labelled Golay code avoiding F8/F12 has
   exactly one normalised pi, so COUNT mode counts labelled codes.
   usage: lab E CODEFILE [first [max]]      forbidden families from each code (layout B lines)
          lab F F8BIN F12BIN                raw 2^21-byte bitmaps (bit m of byte m>>3 = mask m)
   env: COUNT=1 (all solutions), PLANT=seed (E mode: plant a random labelled Golay code), C5=c1,c2,c3,c4,c5 */
#include "golay24.h"
#include "f4a.h"
#include <time.h>

static uint8_t *F8, *F12;
#define BGET(b, m) (((b)[(m) >> 3] >> ((m) & 7)) & 1)
#define BSET(b, m) ((b)[(m) >> 3] |= (uint8_t)(1u << ((m) & 7)))
#define BCLR(b, m) ((b)[(m) >> 3] &= (uint8_t)~(1u << ((m) & 7)))

static int octOf[24][253], nOctOf[24];
static int optsOf[759][8];
static int cnt[759]; static uint32_t img[759];
static int pl[24]; static uint32_t dom[24];
static long long nodes, nsol; static uint64_t hsum; static int countmode;
static int p8[8], q1;            /* p8[0..7] = points of O0 increasing; q1 = first point outside O0 */
static uint64_t first_sol_hash; static int planted_found; static uint64_t planted_hash;

static uint64_t code_hash_c3(const uint32_t *B) {   /* same definition as c3class gcore.h code_hash */
    uint32_t R[12]; memcpy(R, B, sizeof R); int r = 0;
    for (int c = 23; c >= 0 && r < 12; c--) {
        int p = -1; for (int i = r; i < 12; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        uint32_t t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < 12; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < 12; i++) { h ^= R[i]; h *= 1099511628211ULL; h ^= h >> 29; }
    return h;
}

static void setup_ref(void) {
    golay_build();
    memset(nOctOf, 0, sizeof nOctOf);
    for (int k = 0; k < 759; k++) { int n = 0; for (uint32_t t = OCT[k]; t; t &= t - 1) { int p = __builtin_ctz(t); optsOf[k][n++] = p; octOf[p][nOctOf[p]++] = k; } }
    for (int p = 0; p < 24; p++) if (nOctOf[p] != 253) { fprintf(stderr, "octad incidence wrong\n"); exit(9); }
    uint32_t O0 = OCT[0]; int n = 0; for (uint32_t t = O0; t; t &= t - 1) p8[n++] = __builtin_ctz(t);
    q1 = -1; for (int x = 0; x < 24; x++) if (!((O0 >> x) & 1)) { q1 = x; break; }
}

/* place p at c: returns 1 if consistent; always applies cnt/img updates (undo with unplace) */
static int place(int p, int c) {
    pl[p] = c; int ok = 1; uint32_t bit = 1u << c;
    for (int u = 0; u < 24; u++) if (pl[u] < 0) { dom[u] &= ~bit; if (!dom[u]) ok = 0; }
    for (int j = 0; j < 253; j++) {
        int k = octOf[p][j]; cnt[k]++; img[k] |= bit;
        if (!ok) continue;
        if (cnt[k] == 8) { if (BGET(F8, img[k])) ok = 0; }
        else if (cnt[k] == 7) {
            int u = -1; for (int t = 0; t < 8; t++) if (pl[optsOf[k][t]] < 0) { u = optsOf[k][t]; break; }
            uint32_t keep = 0;
            for (uint32_t d = dom[u]; d; d &= d - 1) { uint32_t f = d & -d; if (!BGET(F8, img[k] | f)) keep |= f; }
            dom[u] = keep; if (!keep) ok = 0;
        }
    }
    return ok;
}
static void unplace(int p) {
    uint32_t bit = 1u << pl[p];
    for (int j = 0; j < 253; j++) { int k = octOf[p][j]; cnt[k]--; img[k] &= ~bit; }
    pl[p] = -1;
}

static void leaf(void) {
    for (int k = 0; k < 759; k++) if (BGET(F8, img[k])) { fprintf(stderr, "BUG: forbidden octad at leaf\n"); exit(7); }
    int pm[24]; for (int p = 0; p < 24; p++) pm[p] = pl[p];
    for (int k = 0; k < 2576; k++) if (BGET(F12, perm_apply(pm, DOD[k]))) return;
    uint32_t B[12]; for (int i = 0; i < 12; i++) B[i] = perm_apply(pm, GB[i]);
    uint64_t h = code_hash_c3(B);
    if (nsol == 0) first_sol_hash = h;
    if (h == planted_hash) planted_found = 1;
    nsol++; hsum += h;
}

static int stopflag;
static void search(int nplaced) {
    nodes++;
    if (stopflag) return;
    if (nplaced == 24) { leaf(); if (!countmode && nsol) stopflag = 1; return; }
    int best = -1, bc = 99;
    for (int u = 0; u < 24; u++) if (pl[u] < 0) { int c = __builtin_popcount(dom[u]); if (c < bc) { bc = c; best = u; } }
    uint32_t save[24]; memcpy(save, dom, sizeof save);
    for (uint32_t d = save[best]; d; d &= d - 1) {
        int c = __builtin_ctz(d);
        if (place(best, c)) search(nplaced + 1);
        unplace(best); memcpy(dom, save, sizeof save);
        if (stopflag) return;
    }
}

static void run_instance(const char *id, const int *c5in) {
    nodes = 0; nsol = 0; hsum = 0; stopflag = 0; first_sol_hash = 0; planted_found = 0;
    memset(cnt, 0, sizeof cnt); memset(img, 0, sizeof img);
    for (int p = 0; p < 24; p++) { pl[p] = -1; dom[p] = 0xffffffu; }
    /* choose c1..c5: 5-set with the fewest allowed 8-sets through it (or given) */
    int c5[5];
    if (c5in) memcpy(c5, c5in, sizeof c5);
    else {
        int bestn = 1 << 30; uint32_t bestS = 0;
        for (uint32_t S = 0x1f; S < (1u << 24); ) {
            int n = 0;
            uint32_t rest = 0xffffffu & ~S;
            /* count allowed 8-sets S u {a<b<c} */
            int r[19], nr = 0; for (uint32_t t = rest; t; t &= t - 1) r[nr++] = __builtin_ctz(t);
            for (int a = 0; a < nr && n < bestn; a++) for (int b = a + 1; b < nr; b++) for (int c = b + 1; c < nr; c++)
                if (!BGET(F8, S | (1u << r[a]) | (1u << r[b]) | (1u << r[c]))) n++;
            if (n < bestn) { bestn = n; bestS = S; }
            uint32_t t = S | (S - 1); S = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctz(S) + 1));
        }
        int n = 0; for (uint32_t t = bestS; t; t &= t - 1) c5[n++] = __builtin_ctz(t);
    }
    uint32_t S5 = 0; for (int i = 0; i < 5; i++) S5 |= 1u << c5[i];
    int ok = 1;
    for (int i = 0; i < 5; i++) if (!place(p8[i], c5[i])) ok = 0;
    if (ok) {
        uint32_t save[24]; memcpy(save, dom, sizeof save);
        int r[19], nr = 0; for (uint32_t t = 0xffffffu & ~S5; t; t &= t - 1) r[nr++] = __builtin_ctz(t);
        for (int a = 0; a < nr && !stopflag; a++) for (int b = a + 1; b < nr && !stopflag; b++) for (int c = b + 1; c < nr && !stopflag; c++) {
            uint32_t F = S5 | (1u << r[a]) | (1u << r[b]) | (1u << r[c]);
            if (BGET(F8, F)) continue;
            for (int sw = 0; sw < 2 && !stopflag; sw++) {
                int y6 = r[a], y7 = sw ? r[c] : r[b], y8 = sw ? r[b] : r[c];   /* pi(p6) = min */
                int o1 = place(p8[5], y6), o2 = o1 && place(p8[6], y7), o3 = o2 && place(p8[7], y8);
                if (o3) {
                    uint32_t freec = 0xffffffu; for (int p = 0; p < 24; p++) if (pl[p] >= 0) freec &= ~(1u << pl[p]);
                    int cq = __builtin_ctz(freec);                       /* N3 */
                    if (dom[q1] & (1u << cq)) { uint32_t sv2[24]; memcpy(sv2, dom, sizeof sv2); if (place(q1, cq)) search(9); unplace(q1); memcpy(dom, sv2, sizeof sv2); }
                }
                if (pl[p8[7]] >= 0) unplace(p8[7]);
                if (pl[p8[6]] >= 0) unplace(p8[6]);
                if (pl[p8[5]] >= 0) unplace(p8[5]);
                memcpy(dom, save, sizeof save);
            }
        }
    }
    printf("id=%s res=%s nsol=%lld%s hash=%016llx nodes=%lld c5=%d,%d,%d,%d,%d", id, nsol ? "SAT" : "UNSAT", nsol,
           (!countmode && nsol) ? "+" : "", (unsigned long long)hsum, nodes, c5[0], c5[1], c5[2], c5[3], c5[4]);
}

/* forbidden families from a code: all 4^12 words */
static long long nw8, nw10, nw12;
static uint32_t *S8L, *S10L; static int nS8, nS10;
static void enum_words(const v24 *g, int t, v24 cur) {
    if (t == 12) {
        int w = vwt(cur);
        if (w == 8 || w == 10 || w == 12) {
            uint32_t s = vsupp(cur);
            /* projective: count each support once per projective word: first nonzero coordinate value 1 */
            int c = __builtin_ctz(s); if (vget(cur, c) != 1) return;
            if (w == 8) { nw8++; S8L[nS8++] = s; }
            else if (w == 10) { nw10++; S10L[nS10++] = s; }
            else { nw12++; BSET(F12, s); }
        } else if (w > 0 && w < 8) { fprintf(stderr, "word of weight %d\n", w); exit(5); }
        return;
    }
    for (int s = 0; s < 4; s++) enum_words(g, t + 1, s ? vadd(cur, vscal(g[t], s)) : cur);
}
static void build_from_code(const v24 *rows) {
    memset(F8, 0, 1u << 21); memset(F12, 0, 1u << 21);
    nw8 = nw10 = nw12 = 0; nS8 = nS10 = 0;
    v24 z = { 0, 0 }; enum_words(rows, 0, z);
    for (int j = 0; j < nS8; j++) {
        uint32_t s = S8L[j]; BSET(F8, s);
        for (uint32_t a = s; a; a &= a - 1) for (uint32_t b = 0xffffffu & ~s; b; b &= b - 1) BSET(F8, (s & ~(a & -a)) | (b & -b));
    }
    for (int j = 0; j < nS10; j++) {
        uint32_t s = S10L[j];
        for (uint32_t a = s; a; a &= a - 1) for (uint32_t b = a & (a - 1); b; b &= b - 1) BSET(F8, s & ~(a & -a) & ~(b & -b));
    }
}
static uint64_t rng_s;
static uint64_t rnd(void) { rng_s += 0x9e3779b97f4a7c15ULL; uint64_t z = rng_s; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
static void plant(uint64_t seed) {
    rng_s = seed * 7919 + 12345;
    int pm[24]; for (int i = 0; i < 24; i++) pm[i] = i;
    for (int i = 23; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
    for (int k = 0; k < 759; k++) BCLR(F8, perm_apply(pm, OCT[k]));
    for (int k = 0; k < 2576; k++) BCLR(F12, perm_apply(pm, DOD[k]));
    uint32_t B[12]; for (int i = 0; i < 12; i++) B[i] = perm_apply(pm, GB[i]);
    planted_hash = code_hash_c3(B);
}
static long long popcnt_bitmap(const uint8_t *b) { long long n = 0; for (size_t i = 0; i < (1u << 21); i++) n += __builtin_popcount(b[i]); return n; }

int main(int argc, char **argv) {
    setup_ref();
    F8 = calloc(1u << 21, 1); F12 = calloc(1u << 21, 1);
    S8L = malloc(sizeof(uint32_t) * 10000); S10L = malloc(sizeof(uint32_t) * 40000);
    countmode = getenv("COUNT") && atoi(getenv("COUNT")) == 1;
    const char *plants = getenv("PLANT");
    int c5g[5], *c5p = NULL;
    if (getenv("C5")) { if (sscanf(getenv("C5"), "%d,%d,%d,%d,%d", &c5g[0], &c5g[1], &c5g[2], &c5g[3], &c5g[4]) == 5) c5p = c5g; }
    if (argc >= 4 && !strcmp(argv[1], "F")) {
        FILE *a = fopen(argv[2], "rb"), *b = fopen(argv[3], "rb");
        if (!a || !b || fread(F8, 1, 1u << 21, a) != (1u << 21) || fread(F12, 1, 1u << 21, b) != (1u << 21)) { fprintf(stderr, "bitmap read error\n"); return 1; }
        planted_hash = 0;
        clock_t t0 = clock();
        run_instance("F", c5p);
        printf(" f8=%lld f12=%lld cpu=%.2f\n", popcnt_bitmap(F8), popcnt_bitmap(F12), (double)(clock() - t0) / CLOCKS_PER_SEC);
        return 0;
    }
    if (argc >= 3 && !strcmp(argv[1], "E")) {
        FILE *f = fopen(argv[2], "r"); if (!f) { perror("open"); return 1; }
        long first = argc > 3 ? atol(argv[3]) : 0, max = argc > 4 ? atol(argv[4]) : (1L << 40);
        static char line[16384]; long ln = -1, done = 0;
        while (fgets(line, sizeof line, f) && done < max) {
            ln++; if (ln < first) continue;
            v24 rows[12]; if (!parse_rows_B(line, rows, 12)) { printf("id=%ld res=ERROR parse\n", ln); done++; continue; }
            char id[64]; char *q = strstr(line, "id="); if (q) sscanf(q + 3, "%63s", id); else snprintf(id, sizeof id, "%ld", ln);
            clock_t t0 = clock();
            build_from_code(rows);
            planted_hash = 0;
            if (plants) plant((uint64_t)atoll(plants) + (uint64_t)ln);
            if (getenv("DUMP")) {   /* write the instance as raw bitmaps DUMP_<id>.f8 / .f12 and skip the search */
                char fn[4096]; snprintf(fn, sizeof fn, "%s_%s.f8", getenv("DUMP"), id); FILE *o = fopen(fn, "wb"); fwrite(F8, 1, 1u << 21, o); fclose(o);
                snprintf(fn, sizeof fn, "%s_%s.f12", getenv("DUMP"), id); o = fopen(fn, "wb"); fwrite(F12, 1, 1u << 21, o); fclose(o);
                printf("id=%s dumped planted_hash=%016llx f8=%lld f12=%lld\n", id, (unsigned long long)planted_hash, popcnt_bitmap(F8), popcnt_bitmap(F12));
                fflush(stdout); done++; continue;
            }
            run_instance(id, c5p);
            printf(" pw8=%lld pw10=%lld pw12=%lld f8=%lld f12=%lld", nw8, nw10, nw12, popcnt_bitmap(F8), popcnt_bitmap(F12));
            if (plants) printf(" planted_hash=%016llx planted_found=%d", (unsigned long long)planted_hash, planted_found);
            printf(" cpu=%.2f\n", (double)(clock() - t0) / CLOCKS_PER_SEC);
            fflush(stdout); done++;
        }
        return 0;
    }
    fprintf(stderr, "usage: lab E CODEFILE [first [max]] | lab F F8BIN F12BIN\n"); return 1;
}
