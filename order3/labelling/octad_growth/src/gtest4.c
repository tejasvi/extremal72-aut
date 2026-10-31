/* Golay-labelling test v4 = v3 with table-driven level-3 / A-test.
   Search (each step: the unique octad of G through a chosen 5-set, or the unique tetrad of a sextet):
     L1: O1 = octad through a root 5-set F0 (few allowed 8-sets through F0).
     L2: O2 = octad through T' u {x} (T' a 4-subset of O1, x outside; 455 options), 5-set chosen by min count
         among a sample.  T = O1 & O2, A = O1 \ T, B = O2 \ T, X = the other 12 points.
     L2 node: A, B are tetrads of the sextet of T in G; the tetrad C of that sextet containing a chosen x in X
         must have T u C, A u C, B u C, X \ C allowed (table over all 495 4-subsets of X; x = point with the
         fewest valid C).  For each valid C: A-test on the 16 points T u A u B u C (octad R = X \ C): the octads
         of G disjoint from R form, with Omega, a 6-dim code whose 3 nontrivial cosets over <Omega, T u A, T u B,
         T u C> consist of the octads pi_T u pi_A u pi_B u pi_C (pairs from one fixed pair-partition per column,
         an even number of complemented pairs relative to a parity); partitions are distinct per column across
         the 3 cosets and c3 = c1 + c2.
         Coset validity via forbidden-pair tables: for each 6-set X6 = pi_T u pi_A u pi_B, FP(X6) = pairs pi in X
         with X6 u pi forbidden, computed from the supports of E (W10: weight-10 supports containing X6; W8:
         weight-8 supports meeting X6 in 6 or 5 points) or, in the random-table modes, by lookups.
     Then generic octad growth from the 6-dim code (gcore.h ext_search) to dim 12.
   Modes:  E file [maxcodes] [first]   (DEBUGFP=1: also compute FP by lookups and assert equality)
           P dens seed [dens12]        planted
           Z dens seed [dens12]        sextet-restricted (compare with gbfs)                                  */
#include "gcore.h"

static long nL[8], nK4, nApass, nFPdiff; static double tStart;
static int use_incidence = 0, debugfp = 0, sample2 = 24;

/* ---- support indexes (CSR by subset rank) ---- */
static int *i10_6s, *i10_6, *i8_6s, *i8_6, *i8_5s, *i8_5;
static void build_csr(const uint32_t *sup, int ns, int k, int nsub, int **startp, int **listp) {
    int nranks = binom_(24, k);
    int *start = calloc(nranks + 1, sizeof(int));
    uint32_t pats[256]; int np = 0;
    int w = sup && ns ? __builtin_popcount(sup[0]) : 0;
    for (uint32_t p = 0; p < (1u << w); p++) if (__builtin_popcount(p) == k) pats[np++] = p;
    (void)nsub;
    for (int i = 0; i < ns; i++) for (int j = 0; j < np; j++) start[srank(_pdep_u32(pats[j], sup[i])) + 1]++;
    for (int r = 0; r < nranks; r++) start[r + 1] += start[r];
    int *list = malloc(sizeof(int) * (start[nranks] + 1)); int *fill = malloc(sizeof(int) * nranks);
    memcpy(fill, start, sizeof(int) * nranks);
    for (int i = 0; i < ns; i++) for (int j = 0; j < np; j++) list[fill[srank(_pdep_u32(pats[j], sup[i]))]++] = i;
    free(fill);
    *startp = start; *listp = list;
}
static void build_indexes(void) {
    if (i10_6s) { free(i10_6s); free(i10_6); free(i8_6s); free(i8_6); free(i8_5s); free(i8_5); }
    build_csr(E_s10, E_n10, 6, 210, &i10_6s, &i10_6);
    build_csr(E_s8, E_n8, 6, 28, &i8_6s, &i8_6);
    build_csr(E_s8, E_n8, 5, 56, &i8_5s, &i8_5);
}

/* ---- L2-node tables ---- */
static int xidx[24]; static uint32_t Xmask; static int xpts[12];
static uint32_t cpt[3][4], cref[3][3], ccmp[3][3];       /* columns T, A, B */
static uint64_t FPw[216][3];
static uint64_t Uw[27][2][3];
static uint64_t clos[4096][3], star[4096][3];
static inline void pbit(uint64_t *w, int i, int j) { int b = i * 16 + j; w[b >> 6] |= 1ULL << (b & 63); b = j * 16 + i; w[b >> 6] |= 1ULL << (b & 63); }
static inline int gbit(const uint64_t *w, int i, int j) { int b = i * 16 + j; return (w[b >> 6] >> (b & 63)) & 1; }
static void init_closures(void) {
    for (int s = 0; s < 4096; s++) {
        memset(clos[s], 0, 24); memset(star[s], 0, 24);
        for (int i = 0; i < 12; i++) if ((s >> i) & 1) {
            for (int j = i + 1; j < 12; j++) if ((s >> j) & 1) pbit(clos[s], i, j);
            for (int j = 0; j < 12; j++) if (j != i) pbit(star[s], i, j);
        }
    }
}
static uint32_t pat4_12[495];
static inline uint32_t colpair(int col, int q) { return (q & 1) ? ccmp[col][q >> 1] : cref[col][q >> 1]; }
static void fp_lookup(uint32_t X6, uint64_t *w) {
    memset(w, 0, 24);
    for (int i = 0; i < 12; i++) for (int j = i + 1; j < 12; j++) if (F8(X6 | (1u << xpts[i]) | (1u << xpts[j]))) pbit(w, i, j);
}
static void fp_incidence(uint32_t X6, uint64_t *w) {
    uint64_t w0 = 0, w1 = 0, w2 = 0;
    uint32_t r6 = srank(X6);
    for (int t = i10_6s[r6]; t < i10_6s[r6 + 1]; t++) {
        uint32_t s = _pext_u32(E_s10[i10_6[t]], Xmask);
        w0 |= clos[s][0]; w1 |= clos[s][1]; w2 |= clos[s][2];
    }
    for (int t = i8_6s[r6]; t < i8_6s[r6 + 1]; t++) {
        uint32_t s = _pext_u32(E_s8[i8_6[t]] & ~X6, Xmask);
        w0 |= star[s][0]; w1 |= star[s][1]; w2 |= star[s][2];
    }
    for (uint32_t m = X6; m; m &= m - 1) {
        uint32_t Y = X6 & ~(m & -m); uint32_t r5 = srank(Y);
        for (int t = i8_5s[r5]; t < i8_5s[r5 + 1]; t++) {
            uint32_t S = E_s8[i8_5[t]];
            if ((S & X6) != Y) continue;
            uint32_t s = _pext_u32(S & ~X6, Xmask);
            w0 |= clos[s][0]; w1 |= clos[s][1]; w2 |= clos[s][2];
        }
    }
    w[0] = w0; w[1] = w1; w[2] = w2;
}
static void build_L2_tables(uint32_t T, uint32_t A, uint32_t B) {
    uint32_t cols[3] = { T, A, B };
    for (int i = 0; i < 3; i++) {
        uint32_t m = cols[i]; int j = 0;
        for (; m; m &= m - 1) cpt[i][j++] = 1u << __builtin_ctz(m);
        for (int k = 0; k < 3; k++) { cref[i][k] = cpt[i][0] | cpt[i][k + 1]; ccmp[i][k] = cols[i] ^ cref[i][k]; }
    }
    for (int qT = 0; qT < 6; qT++) for (int qA = 0; qA < 6; qA++) for (int qB = 0; qB < 6; qB++) {
        uint32_t X6 = colpair(0, qT) | colpair(1, qA) | colpair(2, qB);
        int id = qT * 36 + qA * 6 + qB;
        if (use_incidence) {
            fp_incidence(X6, FPw[id]);
            if (debugfp) { uint64_t r2[3]; fp_lookup(X6, r2); if (memcmp(r2, FPw[id], 24)) nFPdiff++; }
        } else fp_lookup(X6, FPw[id]);
    }
    for (int kT = 0; kT < 3; kT++) for (int kA = 0; kA < 3; kA++) for (int kB = 0; kB < 3; kB++) {
        int kk = (kT * 3 + kA) * 3 + kB;
        memset(Uw[kk], 0, sizeof Uw[kk]);
        for (int e = 0; e < 8; e++) {
            int s = __builtin_popcount(e) & 1;
            int id = (2 * kT + (e & 1)) * 36 + (2 * kA + ((e >> 1) & 1)) * 6 + (2 * kB + ((e >> 2) & 1));
            for (int r = 0; r < 3; r++) Uw[kk][s][r] |= FPw[id][r];
        }
    }
}
static int cc[4];
static uint32_t coset_rep4(const int *k, int p, uint32_t C) {
    uint32_t O = cref[0][k[0]] | cref[1][k[1]] | cref[2][k[2]];
    uint32_t c0 = 1u << xpts[cc[0]], ck = 1u << xpts[cc[k[3] + 1]];
    uint32_t ref = c0 | ck;
    return O | (p ? (C ^ ref) : ref);
}
static uint8_t cb6[27];
static void precompute_C_bits(void) {
    int r0[3], r1[3], o0[3], o1[3];
    for (int k = 0; k < 3; k++) {
        r0[k] = cc[0]; r1[k] = cc[k + 1]; int a = -1, b = -1;
        for (int t = 1; t < 4; t++) if (t != k + 1) { if (a < 0) a = cc[t]; else b = cc[t]; }
        o0[k] = a; o1[k] = b;
    }
    for (int kk = 0; kk < 27; kk++) {
        const uint64_t *U0 = Uw[kk][0], *U1 = Uw[kk][1]; uint8_t bits = 0;
        for (int k = 0; k < 3; k++) {
            int ref0 = gbit(U0, r0[k], r1[k]), ref1 = gbit(U1, r0[k], r1[k]);
            int cmp0 = gbit(U0, o0[k], o1[k]), cmp1 = gbit(U1, o0[k], o1[k]);
            if (!ref0 && !cmp1) bits |= (uint8_t)(1u << (2 * k));
            if (!cmp0 && !ref1) bits |= (uint8_t)(1u << (2 * k + 1));
        }
        cb6[kk] = bits;
    }
}
#define CV(kT, kA, kB, kC, p) ((cb6[((kT) * 3 + (kA)) * 3 + (kB)] >> (2 * (kC) + (p))) & 1)
static double tAT, tEXT, tV3, tFP;
static void atest(uint32_t T, uint32_t A, uint32_t B, uint32_t C) {
    nK4++;
    precompute_C_bits();
    int k1[4], k2[4], k3[4];
    k1[0] = 0; k2[0] = 1; k3[0] = 2;
    for (k1[1] = 0; k1[1] < 3; k1[1]++) for (k1[2] = 0; k1[2] < 3; k1[2]++) for (k1[3] = 0; k1[3] < 3; k1[3]++)
    for (int p1 = 0; p1 < 2; p1++) {
        if (!CV(k1[0], k1[1], k1[2], k1[3], p1)) continue;
        for (int m = 0; m < 8; m++) {
            for (int i = 1; i < 4; i++) {
                int o0 = (k1[i] + 1) % 3, o1 = (k1[i] + 2) % 3;
                k2[i] = ((m >> (i - 1)) & 1) ? o1 : o0;
                k3[i] = 3 - k1[i] - k2[i];
            }
            for (int p2 = 0; p2 < 2; p2++) {
                if (!CV(k2[0], k2[1], k2[2], k2[3], p2)) continue;
                int p3 = p1 ^ p2;
                if (!CV(k3[0], k3[1], k3[2], k3[3], p3)) continue;
                nApass++;
                uint32_t b0[2048], b1[2048], b2[2048];
                uint32_t O3 = T | C, r1 = coset_rep4(k1, p1, C), r2 = coset_rep4(k2, p2, C);
                if (!orth(O3) || !valid_new(O3)) { fprintf(stderr, "inconsistency O3\n"); exit(1); }
                int m0 = addK(O3, b0);
                if (!orth(r1) || !valid_new(r1)) { fprintf(stderr, "inconsistency c1\n"); exit(1); }
                int m1 = addK(r1, b1);
                if (!orth(r2) || !valid_new(r2)) { fprintf(stderr, "inconsistency c2\n"); exit(1); }
                int m2 = addK(r2, b2);
                double te = now();
                ext_search(T | A);
                tEXT += now() - te;
                undoK(b2, m2); undoK(b1, m1); undoK(b0, m0);
            }
        }
    }
}
static void l2node(uint32_t O1, uint32_t O2) {
    uint32_t T = O1 & O2, A = O1 & ~T, B = O2 & ~T;
    Xmask = FULL24 & ~(O1 | O2);
    int k = 0; for (uint32_t m = Xmask; m; m &= m - 1) { xpts[k] = __builtin_ctz(m); xidx[xpts[k]] = k; k++; }
    /* valid C table */
    double ta = now();
    static uint8_t v3[495]; int cnt[12] = { 0 }, nv = 0;
    for (int i = 0; i < 495; i++) {
        uint32_t C = _pdep_u32(pat4_12[i], Xmask);
        v3[i] = !F8(T | C) && !F8(A | C) && !F8(B | C) && !F8(Xmask & ~C);
        if (v3[i]) { nv++; for (uint32_t c = pat4_12[i]; c; c &= c - 1) cnt[__builtin_ctz(c)]++; }
    }
    double tb = now(); tV3 += tb - ta;
    if (!nv) return;
    int bx = 0; for (int i = 1; i < 12; i++) if (cnt[i] < cnt[bx]) bx = i;
    if (!cnt[bx]) return;
    build_L2_tables(T, A, B);
    double tc = now(); tFP += tc - tb;
    for (int i = 0; i < 495; i++) if (v3[i] && ((pat4_12[i] >> bx) & 1)) {
        uint32_t C = _pdep_u32(pat4_12[i], Xmask);
        int j = 0; for (uint32_t c = pat4_12[i]; c; c &= c - 1) cc[j++] = __builtin_ctz(c);
        nL[3]++;
        atest(T, A, B, C);
    }
    tAT += now() - tc;
}
static void level2(uint32_t O1) {
    uint32_t out = FULL24 & ~O1;
    static uint32_t cb[2][455]; int cur = 0, best = 1 << 30;
    int pts_out[16], no = 0; for (uint32_t t = out; t; t &= t - 1) pts_out[no++] = __builtin_ctz(t);
    static uint32_t p3_15[455]; static int init = 0;
    if (!init) { int kk = 0; for (uint32_t p = 0; p < (1u << 15); p++) if (__builtin_popcount(p) == 3) p3_15[kk++] = p; init = 1; }
    for (int s = 0; s < sample2 && best > 0; s++) {
        uint32_t Tp = _pdep_u32(pat4[(s * 29) % 70], O1);
        uint32_t x = 1u << pts_out[(s * 7) % 16];
        uint32_t F = Tp | x, rest = out & ~x;
        int c = 0;
        for (int i = 0; i < 455 && c < best; i++) {
            uint32_t O = F | _pdep_u32(p3_15[i], rest);
            if (valid_new(O)) cb[cur][c++] = O;
        }
        if (c < best) { best = c; cur ^= 1; }
    }
    if (best == 0) return;
    uint32_t keep[455]; int nl = best; memcpy(keep, cb[cur ^ 1], sizeof(uint32_t) * nl);
    for (int i = 0; i < nl; i++) {
        uint32_t buf[2048];
        nL[2]++;
        int m = addK(keep[i], buf);
        l2node(O1, keep[i]);
        undoK(buf, m);
    }
}
static int count_allowed_through(uint32_t F) {
    uint32_t comp = FULL24 & ~F; int c = 0;
    for (int i = 0; i < 969; i++) c += !F8(F | _pdep_u32(pat3_19[i], comp));
    return c;
}
static uint32_t all5[42504];
static uint32_t choose_root(int *bestcnt, int exhaustive) {
    int best = 1 << 30; uint32_t bF = 0;
    if (exhaustive || !E_n10) {
        for (int i = 0; i < 42504; i++) { int c = count_allowed_through(all5[i]); if (c < best) { best = c; bF = all5[i]; } }
    } else {
        static int score[42504]; memset(score, 0, sizeof score);
        static uint32_t pat5_10[252]; static int i2 = 0;
        if (!i2) { int kk = 0; for (uint32_t q = 0; q < 1024; q++) if (__builtin_popcount(q) == 5) pat5_10[kk++] = q; i2 = 1; }
        for (int j = 0; j < E_n10; j++) for (int p = 0; p < 252; p++) score[srank(_pdep_u32(pat5_10[p], E_s10[j]))] += 10;
        for (int j = 0; j < E_n8; j++) for (int p = 0; p < 56; p++) score[srank(_pdep_u32(pat5[p], E_s8[j]))] += 49;
        int top[256], nt = 0;
        for (int i = 0; i < 42504; i++) {
            if (nt < 256) { top[nt++] = i; continue; }
            int mi = 0; for (int t = 1; t < 256; t++) if (score[top[t]] < score[top[mi]]) mi = t;
            if (score[i] > score[top[mi]]) top[mi] = i;
        }
        for (int t = 0; t < nt; t++) { int c = count_allowed_through(all5[top[t]]); if (c < best) { best = c; bF = all5[top[t]]; } }
    }
    *bestcnt = best; return bF;
}
static long nroot;
static void run_test(int exhaustive_root) {
    memset(nodes, 0, sizeof nodes); memset(nL, 0, sizeof nL); nK4 = nApass = nFPdiff = 0; tAT = tEXT = tV3 = tFP = 0; nsol = nchk = 0; nsolstore = 0; solhash = 0;
    resetK();
    int rc; uint32_t F0 = choose_root(&rc, exhaustive_root);
    nroot = rc;
    uint32_t comp = FULL24 & ~F0;
    for (int i = 0; i < 969; i++) {
        uint32_t O1 = F0 | _pdep_u32(pat3_19[i], comp);
        if (F8(O1)) continue;
        uint32_t buf[4];
        nL[1]++;
        int m = addK(O1, buf);
        level2(O1);
        undoK(buf, m);
    }
}
static void report(const char *tag, double dt) {
    printf("%s root=%ld L1=%ld L2=%ld K4=%ld Apass=%ld ext:", tag, nroot, nL[1], nL[2], nK4, nApass);
    for (int d = 7; d < 12; d++) printf(" %ld", nodes[d]);
    printf(" sols=%ld hash=%016llx chk=%ld%s tV3=%.2f tFP=%.2f tAT=%.2f tEXT=%.2f t=%.2fs\n", nsol, (unsigned long long)solhash, nchk, debugfp ? (nFPdiff ? " FPDIFF!" : " fpok") : "", tV3, tFP, tAT - tEXT, tEXT, dt);
    fflush(stdout);
}
int main(int argc, char **argv) {
    gcore_init();
    { int k = 0; for (uint32_t p = 0; p < 4096; p++) if (__builtin_popcount(p) == 4) pat4_12[k++] = p; }
    init_closures();
    { int k = 0; for (uint32_t p = 0; p < (1u << 24); p++) if (__builtin_popcount(p) == 5) all5[k++] = p; }
    if (getenv("MAXSCAN")) maxscan = atoi(getenv("MAXSCAN"));
    if (getenv("SAMPLE2")) sample2 = atoi(getenv("SAMPLE2"));
    if (getenv("DEBUGFP")) debugfp = 1;
    char mode = argv[1][0];
    if (mode == 'E') {
        FILE *f = fopen(argv[2], "r"); long maxc = argc > 3 ? atol(argv[3]) : 1L << 40; long first = argc > 4 ? atol(argv[4]) : 0;
        char line[8192]; long ci = 0;
        use_incidence = getenv("LOOKUPFP") ? 0 : 1;
        while (ci < first + maxc && fgets(line, sizeof line, f)) {
            if (ci++ < first) continue;
            f4v gen[12]; if (!parse_code_line(line, gen)) continue;
            double t0 = now();
            long nf = set_forbidden_from_E(gen);
            if (use_incidence) build_indexes();
            run_test(0);
            char tag[256]; snprintf(tag, sizeof tag, "code %ld n8=%d n10=%d n12=%d forb8=%.3f", ci - 1, E_n8, E_n10, E_n12, nf / 735471.0);
            report(tag, now() - t0);
        }
    } else if (mode == 'P' || mode == 'Z') {
        double dens = atof(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10);
        double dens12 = argc > 4 ? atof(argv[4]) : 0;
        rng_t R; rng_seed(&R, seed);
        uint8_t *keep = calloc(1 << 21, 1);
        uint32_t W[4096]; golay_words(W);
        int p[24]; for (int i = 0; i < 24; i++) p[i] = i;
        uint32_t sext[6]; for (int i = 0; i < 6; i++) sext[i] = 0xFu << (4 * i);
        if (mode == 'P') {
            for (int i = 23; i > 0; i--) { int j = rng_next(&R) % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
            for (int m = 0; m < 4096; m++) SETB(keep, applyperm(p, W[m]));
        } else {
            for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) SETB(keep, sext[i] | sext[j]);
        }
        memset(forb8, 0, F8BYTES); memset(forb12, 0, F12BYTES);
        E_n10 = 0; E_n8 = 0;
        for (uint32_t s = 0; s < (1u << 24); s++) {
            int c = __builtin_popcount(s);
            if (c == 8 && !GETB(keep, s)) {
                int bad = 0;
                if (mode == 'Z') { int par = __builtin_popcount(s & sext[0]) & 1; for (int i = 1; i < 6; i++) if ((__builtin_popcount(s & sext[i]) & 1) != par) bad = 1; }
                if (bad || (rng_next(&R) >> 11) * 0x1.0p-53 < dens) SET8(s);
            }
            if (c == 12 && !GETB(keep, s) && dens12 > 0 && (rng_next(&R) >> 11) * 0x1.0p-53 < dens12) SET12(s);
        }
        double t1 = now();
        run_test(1);
        int found = 0;
        if (mode == 'P') for (int s = 0; s < nsolstore; s++) { int ok = 1; for (int i = 0; i < 12; i++) if (!GETB(keep, solbasis[s][i])) ok = 0; found |= ok; }
        char tag[256]; snprintf(tag, sizeof tag, "%s dens=%.4f seed=%lu found=%d", mode == 'P' ? "planted" : "sextetZ", dens, (unsigned long)seed, found);
        report(tag, now() - t1);
    }
    return 0;
}
