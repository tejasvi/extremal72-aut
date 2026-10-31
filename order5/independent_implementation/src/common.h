/* common.h -- R membership, orbits of rows under H0 = <column perms (GL(3,2)), column mu5-scalings, Frobenius> */
#ifndef COMMON_H
#define COMMON_H
#include "gf16.h"

static int THR = 16;                 /* the bound in (*); 12 for the planted self-test */
static uint8_t ISR[16384];           /* class pattern p is the pattern of a row in R */
static int ORB[16384];               /* orbit index ("key") of an R-pattern, -1 otherwise; key 0 = largest orbit */
static int NORB = 0;
static int ORB_REP[64];              /* representative pattern of each orbit */
static long long ORB_NVEC[64];       /* number of vectors of R in the orbit */
static int ORB_NPAT[64];

/* R: <u,u> = 1 and M(c u) >= THR - wt(c) for all c != 0.  Depends only on the class pattern. */
static int pattern_in_R(int p) {
    if (psumnorm(p) != 1) return 0;
    for (int cc = 1; cc <= 3; cc++) if (MTAB[pscale(p, cc)] < THR - CLSWT[cc]) return 0;
    return 1;
}
static int cmp_orb(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    if (ORB_NVEC[x] != ORB_NVEC[y]) return ORB_NVEC[x] > ORB_NVEC[y] ? -1 : 1;
    return ORB_REP[x] - ORB_REP[y];
}
static void common_init(int thr) {
    THR = thr;
    gf_init(); mu5_init();
    for (int p = 0; p < 16384; p++) { ISR[p] = pattern_in_R(p); ORB[p] = -1; }
    /* orbits of R-patterns under GL(3,2) x <Frobenius>; Frobenius acts on patterns as pfrob (order 2) */
    int tmprep[64]; long long tmpn[64]; int tmpnp[64]; int tmpid[16384];
    for (int p = 0; p < 16384; p++) tmpid[p] = -1;
    int n = 0;
    for (int p = 0; p < 16384; p++) {
        if (!ISR[p] || tmpid[p] >= 0) continue;
        int cnt = 0;
        for (int g = 0; g < 168; g++) for (int f = 0; f < 2; f++) {
            int q = pperm(p, AUT[g]); if (f) q = pfrob(q);
            if (!ISR[q]) { fprintf(stderr, "R not invariant!\n"); exit(1); }
            if (tmpid[q] < 0) { tmpid[q] = n; cnt++; }
        }
        if (n >= 64) { fprintf(stderr, "too many orbits\n"); exit(1); }
        tmprep[n] = p; tmpnp[n] = cnt; tmpn[n] = 0;
        long long v = 1; for (int k = 0; k < pnnz(p); k++) v *= 5;
        tmpn[n] = v * cnt;
        n++;
    }
    NORB = n;
    int idx[64]; for (int i = 0; i < n; i++) { idx[i] = i; ORB_REP[i] = tmprep[i]; ORB_NVEC[i] = tmpn[i]; }
    qsort(idx, n, sizeof(int), cmp_orb);
    int newid[64];
    for (int k = 0; k < n; k++) newid[idx[k]] = k;
    for (int k = 0; k < n; k++) { ORB_REP[k] = tmprep[idx[k]]; ORB_NVEC[k] = tmpn[idx[k]]; ORB_NPAT[k] = tmpnp[idx[k]]; }
    for (int p = 0; p < 16384; p++) if (tmpid[p] >= 0) ORB[p] = newid[tmpid[p]];
}
/* the representative row vector of orbit k: class reps 1 (norm 1), 5 (norm w), 3 (norm w^2) */
static uint32_t orbit_rep_vector(int k) {
    int p = ORB_REP[k]; uint32_t v = 0;
    for (int i = 0; i < 7; i++) v |= (uint32_t)CLS_REP[(p >> (2*i)) & 3] << (4*i);
    return v;
}
static inline int keyof(uint32_t v) { return ORB[npat(v)]; }
#endif
