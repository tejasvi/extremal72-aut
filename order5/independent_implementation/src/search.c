/* search.c -- exhaustive search for unitary U (7x7 over GF(16)) with M(a) + M(aU) >= THR for all a != 0.
 *
 * Canonical form searched (every solution orbit contains at least one such U; see REPORT.md):
 *  (C1) key(row 0) = min key over all rows, and <= min key over all columns   (row perms, conj-transpose)
 *  (C2) row 0 = orbit representative r of its H0-orbit                         (column ops + Frobenius)
 *  (C3) row 1 has minimal key2 among rows 1..6 and row 1 = key2(row 1)         (row perms fixing 0; Stab(r))
 *       where key2(u) = min_{g in Stab(r)} minrep(g u)
 *  (C4) rows 1..6 are mu5-normalised (minimal packed value in their mu5-orbit) (row scalings)
 *  (C5) row 2 has minimal key2 among the rows at positions 2,4,5,6             (row perms fixing 0 and 1)
 * Rows are filled in the order of positions POS[] = 0,1,3,2,4,5,6 (the line {0,1,3} first).
 */
#include "common.h"
#include <omp.h>
#include <sys/time.h>

static const int POS[7] = {0, 1, 3, 2, 4, 5, 6};
static int K0;
static uint32_t RREP;

#include "stab.h"

/* pair condition: for all c0 != 0, c1 in class reps: M2(c0,c1) + M(c0 x + c1 y) >= THR.
   xm = the 16 multiples of x. (c1 = 0 / c0 = 0 cases are membership in R.) */
static int M2T[4][4];   /* THR - M of the 2-supported a with classes (c0,c1) */
static inline int pair_ok(const uint32_t xm[16], uint32_t y) {
    for (int cl = 1; cl <= 3; cl++) {
        uint32_t ym = smul(CLS_REP[cl], y);
        for (int c0 = 1; c0 < 16; c0++)
            if (MTAB[npat(xm[c0] ^ ym)] < M2T[NCLS[c0]][cl]) return 0;
    }
    return 1;
}

/* EXT[d][q]: q (pattern on positions POS[0..d]) extends to an R-pattern of key >= K0 */
static uint8_t EXT[7][16384];
static int DMASK[7];
static void build_ext(void) {
    memset(EXT, 0, sizeof EXT);
    for (int d = 0; d < 7; d++) { DMASK[d] = 0; for (int j = 0; j <= d; j++) DMASK[d] |= 3 << (2 * POS[j]); }
    for (int p = 0; p < 16384; p++) if (ISR[p] && ORB[p] >= K0) for (int d = 0; d < 7; d++) EXT[d][p & DMASK[d]] = 1;
}

static FILE *DUMPF = NULL; static int DUMPD = 0, DUMPMIN = 0;/* optional node dump (tests only) */
static int PAR2 = 0;                                  /* parallel depth-2 loop (node1 mode) */
typedef struct { uint32_t v, k2; } cand_t;
static uint32_t GUIDE[8]; static int NGUIDE = 0;   /* optional: rows forced at depths 2..1+NGUIDE (tests only) */

static cand_t *L1; static long NL1;
static long *NODE1; static long NNODE1;
static int cmp_cand(const void *a, const void *b) {
    const cand_t *x = a, *y = b;
    if (x->k2 != y->k2) return x->k2 < y->k2 ? -1 : 1;
    return x->v < y->v ? -1 : (x->v > y->v);
}

typedef struct {
    uint32_t rows[7];
    uint32_t mult[7][16];
    int colpat[7];
    cand_t *C[8];
    long nC[8];
    long long tested[8], passext[8], nodes[8];
    long long nsol;
    FILE *solf;
} tstate;

static int fc_rec(const tstate *ts, int d, int j, uint32_t v, int apat, int nnz, const uint32_t ym[4]) {
    if (j == d) {
        if (nnz < 2) return 1;
        for (int cl = 1; cl <= 3; cl++)
            if (MTAB[npat(v ^ ym[cl])] + MTAB[apat | (cl << (2 * POS[d]))] < THR) return 0;
        return 1;
    }
    int sh = 2 * POS[j];
    for (int a = 0; a < 16; a++)
        if (!fc_rec(ts, d, j + 1, v ^ ts->mult[j][a], apat | (NCLS[a] << sh), nnz + (a != 0), ym)) return 0;
    return 1;
}
static long long FAILPAIR[7][7][7];   /* [d][j][k] pre-pass failures (racy counters, stats only) */
static long long FAILREC[7];
/* all a supported on POS[0..d] with a_{POS[d]} != 0 and at least two other nonzeros */
static int full_check(const tstate *ts, int d, uint32_t y) {
    uint32_t ym[4];
    for (int cl = 1; cl <= 3; cl++) ym[cl] = smul(CLS_REP[cl], y);
    /* quick pre-pass: exactly two other nonzeros */
    for (int j = 0; j < d; j++) for (int k = j + 1; k < d; k++) {
        int sj = 2 * POS[j], sk = 2 * POS[k];
        for (int aj = 1; aj < 16; aj++) for (int ak = 1; ak < 16; ak++) {
            uint32_t v = ts->mult[j][aj] ^ ts->mult[k][ak];
            int ap = (NCLS[aj] << sj) | (NCLS[ak] << sk);
            for (int cl = 1; cl <= 3; cl++)
                if (MTAB[npat(v ^ ym[cl])] + MTAB[ap | (cl << (2 * POS[d]))] < THR) { FAILPAIR[d][j][k]++; return 0; }
        }
    }
    if (d <= 2) return 1;   /* d = 2: the pre-pass was exhaustive */
    int r = fc_rec(ts, d, 0, 0, 0, 0, ym);
    if (!r) FAILREC[d]++;
    return r;
}


static void dfs(tstate *ts, int d);
/* candidate i of the list at depth d */
static void dfs_cand(tstate *ts, int d, long i) {
    cand_t *C = ts->C[d]; long n = ts->nC[d];
    uint32_t y = C[i].v;
    if (d - 2 < NGUIDE && y != GUIDE[d - 2]) return;
    ts->tested[d]++;
    int newcol[7];
    for (int j = 0; j < 7; j++) {
        newcol[j] = ts->colpat[j] | (NCLS[vget(y, j)] << (2 * POS[d]));
        if (!EXT[d][newcol[j]]) return;
    }
    ts->passext[d]++;
    if (!full_check(ts, d, y)) return;
    ts->nodes[d]++;
    if (DUMPF && d <= DUMPD && d >= DUMPMIN) {
        #pragma omp critical
        {
            fprintf(DUMPF, "NODE d=%d", d);
            for (int j = 0; j < d; j++) fprintf(DUMPF, " %07x", ts->rows[j]);
            fprintf(DUMPF, " %07x\n", y);
        }
    }
    if (d == 6) {
        ts->nsol++;
        uint32_t U[7];
        for (int j = 0; j < 6; j++) U[POS[j]] = ts->rows[j];
        U[POS[6]] = y;
        #pragma omp critical
        {
            fprintf(ts->solf, "SOL K0=%d", K0);
            for (int p = 0; p < 7; p++) fprintf(ts->solf, " %07x", U[p]);
            fprintf(ts->solf, "\n"); fflush(ts->solf);
        }
        return;
    }
    ts->rows[d] = y;
    for (int c = 0; c < 16; c++) ts->mult[d][c] = smul(c, y);
    int savecol[7]; memcpy(savecol, ts->colpat, sizeof savecol); memcpy(ts->colpat, newcol, sizeof newcol);
    uint32_t kmin = (d == 3) ? C[i].k2 : 0;      /* (C5): rows at positions 4,5,6 have key2 >= key2(row 2) */
    cand_t *N = ts->C[d + 1]; long m = 0;
    for (long t = 0; t < n; t++) {
        if (C[t].k2 < kmin) continue;
        if (herm(C[t].v, y)) continue;
        if (!pair_ok(ts->mult[d], C[t].v)) continue;
        N[m++] = C[t];
    }
    ts->nC[d + 1] = m;
    dfs(ts, d + 1);
    memcpy(ts->colpat, savecol, sizeof savecol);
}
static int PARD = 2;          /* node1 mode: depth whose candidate loop is run in parallel (first unguided depth) */
static void dfs_parallel(tstate *ts, int d) {
    long n = ts->nC[d];
    #pragma omp parallel
    {
        tstate t2 = *ts;
        for (int e = 0; e < 8; e++) { t2.tested[e] = t2.passext[e] = t2.nodes[e] = 0; }
        t2.nsol = 0;
        for (int e = d + 1; e < 8; e++) t2.C[e] = malloc((NL1 + 1) * sizeof(cand_t));
        #pragma omp for schedule(dynamic, 1)
        for (long i = 0; i < n; i++) dfs_cand(&t2, d, i);
        #pragma omp critical
        {
            for (int e = 0; e < 8; e++) { ts->tested[e] += t2.tested[e]; ts->passext[e] += t2.passext[e]; ts->nodes[e] += t2.nodes[e]; }
            ts->nsol += t2.nsol;
        }
        for (int e = d + 1; e < 8; e++) free(t2.C[e]);
    }
}
static void dfs(tstate *ts, int d) {
    if (PAR2 && d == PARD) { dfs_parallel(ts, d); return; }
    long n = ts->nC[d];
    for (long i = 0; i < n; i++) dfs_cand(ts, d, i);
}

static void process_node1(tstate *ts, long idx) {
    long start = NODE1[idx];
    uint32_t c = L1[start].v;
    ts->rows[0] = RREP; ts->rows[1] = c;
    for (int k = 0; k < 16; k++) { ts->mult[0][k] = smul(k, RREP); ts->mult[1][k] = smul(k, c); }
    for (int j = 0; j < 7; j++) {
        ts->colpat[j] = (NCLS[vget(RREP, j)] << (2 * POS[0])) | (NCLS[vget(c, j)] << (2 * POS[1]));
        if (!EXT[1][ts->colpat[j]]) return;
    }
    ts->nodes[1]++;
    cand_t *N = ts->C[2]; long m = 0;
    for (long t = start; t < NL1; t++) {
        if (herm(L1[t].v, c)) continue;
        if (!pair_ok(ts->mult[1], L1[t].v)) continue;
        N[m++] = L1[t];
    }
    ts->nC[2] = m;
    dfs(ts, 2);
}

static double now(void) { struct timeval tv; gettimeofday(&tv, NULL); return tv.tv_sec + 1e-6 * tv.tv_usec; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: search THR K0 [all | sample N seed | range a b] [solfile]\n"); return 1; }
    int thr = atoi(argv[1]); K0 = atoi(argv[2]);
    const char *mode = argc > 3 ? argv[3] : "all";
    common_init(thr);
    double t0 = now();
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) M2T[a][b] = THR - MTAB[a | (b << 2)];
    /* check the pair M is position independent (2-transitivity) */
    for (int a = 1; a < 4; a++) for (int b = 1; b < 4; b++) for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) if (i != j)
        if (MTAB[(a << (2 * i)) | (b << (2 * j))] != MTAB[a | (b << 2)]) { fprintf(stderr, "pair M depends on positions\n"); return 1; }
    /* check (C5) prerequisite: Stab(0,1) in GL(3,2) is transitive on {2,4,5,6} */
    { int seen = 0; for (int g = 0; g < 168; g++) if (AUT[g][0] == 0 && AUT[g][1] == 1) seen |= 1 << AUT[g][2];
      if (seen != ((1 << 2) | (1 << 4) | (1 << 5) | (1 << 6))) { fprintf(stderr, "Stab(0,1) orbit of 2 = %x\n", seen); return 1; } }
    if (K0 < 0 || K0 >= NORB) { fprintf(stderr, "bad K0 (NORB=%d)\n", NORB); return 1; }
    if (getenv("GUIDE")) { char *g = strdup(getenv("GUIDE")), *tok = strtok(g, " ,");
        while (tok && NGUIDE < 5) { GUIDE[NGUIDE++] = strtoul(tok, 0, 16); tok = strtok(NULL, " ,"); } }
    if (getenv("DUMP")) { DUMPF = fopen(getenv("DUMP"), "w"); DUMPD = getenv("DUMPD") ? atoi(getenv("DUMPD")) : 3; DUMPMIN = getenv("DUMPMIN") ? atoi(getenv("DUMPMIN")) : 0; }
    RREP = orbit_rep_vector(K0);
    build_stab(RREP);
    build_ext();
    printf("THR=%d K0=%d r=%07x NORB=%d |Stab(r)|=%d\n", THR, K0, RREP, NORB, NSTAB);
    /* L1: mu5-normalised u in R, key(u) >= K0, <r,u> = 0, pair condition with r */
    uint32_t rm[16]; for (int c = 0; c < 16; c++) rm[c] = smul(c, RREP);
    int nth = omp_get_max_threads();
    cand_t **buf = calloc(nth, sizeof *buf); long *bn = calloc(nth, sizeof *bn), *bcap = calloc(nth, sizeof *bcap);
    #pragma omp parallel
    {
        int t = omp_get_thread_num();
        bcap[t] = 1 << 16; buf[t] = malloc(bcap[t] * sizeof(cand_t));
        #pragma omp for schedule(dynamic, 1)
        for (uint32_t hi = 0; hi < (1u << 12); hi++) for (uint32_t lo = 0; lo < (1u << 16); lo++) {
            uint32_t u = (hi << 16) | lo;
            if (herm(RREP, u)) continue;
            int p = npat(u);
            if (!ISR[p] || ORB[p] < K0) continue;
            if (minrep(u) != u) continue;
            if (!pair_ok(rm, u)) continue;
            if (bn[t] == bcap[t]) { bcap[t] *= 2; buf[t] = realloc(buf[t], bcap[t] * sizeof(cand_t)); }
            buf[t][bn[t]].v = u; buf[t][bn[t]].k2 = 0; bn[t]++;
        }
    }
    NL1 = 0; for (int t = 0; t < nth; t++) NL1 += bn[t];
    L1 = malloc(NL1 * sizeof(cand_t));
    { long k = 0; for (int t = 0; t < nth; t++) { memcpy(L1 + k, buf[t], bn[t] * sizeof(cand_t)); k += bn[t]; free(buf[t]); } }
    #pragma omp parallel for schedule(dynamic, 1024)
    for (long i = 0; i < NL1; i++) L1[i].k2 = key2of(L1[i].v);
    for (long i = 0; i < NL1; i += 1 + NL1 / 2000) if (L1[i].k2 != key2of_slow(L1[i].v)) { fprintf(stderr, "key2 mismatch\n"); return 1; }
    qsort(L1, NL1, sizeof(cand_t), cmp_cand);
    NODE1 = malloc(NL1 * sizeof(long)); NNODE1 = 0;
    for (long i = 0; i < NL1; i++) if (L1[i].v == L1[i].k2) {
        if (i > 0 && L1[i - 1].k2 == L1[i].k2) { fprintf(stderr, "sort order broken\n"); return 1; }
        NODE1[NNODE1++] = i;
    }
    printf("|L1| (mu5-classes) = %ld, depth-1 nodes (Stab(r)-canonical second rows) = %ld, setup %.1fs\n", NL1, NNODE1, now() - t0);
    fflush(stdout);
    /* choose the depth-1 nodes to process */
    long *todo = malloc(NNODE1 * sizeof(long)); long ntodo = 0;
    if (!strcmp(mode, "all")) { for (long i = 0; i < NNODE1; i++) todo[ntodo++] = i; }
    else if (!strcmp(mode, "sample")) {
        long N = atol(argv[4]); uint64_t s = strtoull(argv[5], 0, 10) * 2654435761ULL + 1;
        for (long k = 0; k < N; k++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; todo[ntodo++] = s % NNODE1; }
    } else if (!strcmp(mode, "node1")) {
        uint32_t c = strtoul(argv[4], 0, 16);
        for (long i = 0; i < NNODE1; i++) if (L1[NODE1[i]].v == c) todo[ntodo++] = i;
        if (!ntodo) { printf("NODE1 NOT FOUND %07x (in L1: %d)\n", c, 0); return 2; }
    } else if (!strcmp(mode, "mod")) {
        long m = atol(argv[4]), r0 = atol(argv[5]);
        for (long i = r0; i < NNODE1; i += m) todo[ntodo++] = i;
    } else if (!strcmp(mode, "range")) {
        long a = atol(argv[4]), b = atol(argv[5]); if (b > NNODE1) b = NNODE1;
        for (long i = a; i < b; i++) todo[ntodo++] = i;
    }
    const char *solfn = getenv("SOLFILE") ? getenv("SOLFILE") : "/dev/stdout";
    FILE *solf = fopen(solfn, "a");
    long long tot_tested[8] = {0}, tot_passext[8] = {0}, tot_nodes[8] = {0}, tot_sol = 0;
    double ctime = 0; double t1 = now();
    long done = 0;
    if (!strcmp(mode, "node1")) {
        PAR2 = 1; PARD = 2 + NGUIDE; if (PARD > 6) PARD = 6;
        tstate ts; memset(&ts, 0, sizeof ts); ts.solf = solf;
        for (int d = 2; d < 8; d++) ts.C[d] = malloc((NL1 + 1) * sizeof(cand_t));
        process_node1(&ts, todo[0]);
        for (int d = 0; d < 8; d++) { tot_tested[d] = ts.tested[d]; tot_passext[d] = ts.passext[d]; tot_nodes[d] = ts.nodes[d]; }
        tot_sol = ts.nsol; ctime = now() - t1;
    }
    long nproc = ntodo;
    if (PAR2) ntodo = 0;
    #pragma omp parallel reduction(+:ctime)
    {
        tstate ts; memset(&ts, 0, sizeof ts); ts.solf = solf;
        for (int d = 2; d < 8; d++) ts.C[d] = malloc((NL1 + 1) * sizeof(cand_t));
        #pragma omp for schedule(dynamic, 1)
        for (long k = 0; k < ntodo; k++) {
            double a = now();
            process_node1(&ts, todo[k]);
            ctime += now() - a;
            long dn;
            #pragma omp atomic capture
            dn = ++done;
            if (dn % 1000 == 0) { printf("  progress %ld/%ld  %.0fs\n", dn, ntodo, now() - t1); fflush(stdout); }
        }
        #pragma omp critical
        {
            for (int d = 0; d < 8; d++) { tot_tested[d] += ts.tested[d]; tot_passext[d] += ts.passext[d]; tot_nodes[d] += ts.nodes[d]; }
            tot_sol += ts.nsol;
        }
        for (int d = 2; d < 8; d++) free(ts.C[d]);
    }
    printf("processed %ld depth-1 nodes in %.1fs wall, %.1f thread-s (%.4f thread-s per node)\n", nproc, now() - t1, ctime, ctime / (nproc ? nproc : 1));
    if (!strcmp(mode, "sample")) printf("ESTIMATE full K0=%d: %.1f thread-hours\n", K0, ctime / nproc * NNODE1 / 3600.0);
    printf("depth  position  tested  pass_colext  nodes(passed (*))\n");
    printf("  1      %d      %ld   -   %lld\n", POS[1], NNODE1, tot_nodes[1]);
    for (int d = 2; d < 7; d++) printf("  %d      %d      %lld   %lld   %lld\n", d, POS[d], tot_tested[d], tot_passext[d], tot_nodes[d]);
    for (int d = 2; d < 7; d++) {
        printf("fail stats depth %d: rec %lld; pairs:", d, FAILREC[d]);
        for (int j = 0; j < d; j++) for (int k = j + 1; k < d; k++) printf(" (%d,%d)%s:%lld", POS[j], POS[k], "", FAILPAIR[d][j][k]);
        printf("\n");
    }
    printf("SOLUTIONS %lld\n", tot_sol);
    if (DUMPF) fclose(DUMPF);
    return 0;
}
