/* planted.c -- planted-solution self-test.
 * 1. Generate random unitary U (rows chosen at random one by one, natural order 0..6) satisfying
 *    M(a) + M(aU) >= THR for all a != 0 (checked by brute force over ALL a, no symmetry used).
 * 2. Bring U to the canonical form (C1)-(C5) searched by search.c, by explicitly applying symmetries.
 * 3. Print the canonical matrix and the arguments with which search.c must find it.
 * usage: planted THR NUM SEED */
#include "stab.h"
#include <omp.h>

static uint64_t rs;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* brute force: all a with support in {0..i}, a_i != 0 (no reduction by scalars) */
static int partial_ok(const uint32_t *U, int i) {
    uint32_t mult[7][16];
    for (int j = 0; j <= i; j++) for (int c = 0; c < 16; c++) mult[j][c] = smul(c, U[j]);
    long n = 1L << (4 * i);
    int bad = 0;
    #pragma omp parallel for reduction(|:bad) schedule(static)
    for (long lo = 0; lo < n; lo++) {
        if (bad) continue;
        uint32_t v = 0; uint32_t a = (uint32_t)lo;
        for (int j = 0; j < i; j++) v ^= mult[j][(lo >> (4 * j)) & 15];
        for (int c = 1; c < 16; c++) {
            uint32_t aa = a | ((uint32_t)c << (4 * i));
            if (Mvec(aa) + Mvec(v ^ mult[i][c]) < THR) { bad = 1; break; }
        }
    }
    return !bad;
}
/* brute force over every nonzero a in GF(16)^7 */
static int full_ok(const uint32_t *U) { return partial_ok(U, 6) && partial_ok(U, 5) && partial_ok(U, 4) && partial_ok(U, 3) && partial_ok(U, 2) && partial_ok(U, 1) && partial_ok(U, 0); }
static int is_unitary(const uint32_t *U) {
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) if (herm(U[i], U[j]) != (i == j)) return 0;
    return 1;
}
static uint32_t column(const uint32_t *U, int j) { uint32_t c = 0; for (int i = 0; i < 7; i++) c |= (uint32_t)vget(U[i], j) << (4 * i); return c; }

static int MINK = 0;   /* optional: only rows/columns of key >= MINK (to exercise K0 > 0) */
static int gen(uint32_t *U) {
    for (int i = 0; i < 7; i++) {
        int found = 0;
        for (int tries = 0; tries < 400 && !found; tries++) {
            uint32_t v = (uint32_t)rnd64() & 0x0FFFFFFF;
            for (int j = 0; j < i; j++) v ^= smul(herm(v, U[j]), U[j]);   /* project onto rows^perp */
            for (int j = 0; j < i; j++) if (herm(v, U[j])) { fprintf(stderr, "projection bug\n"); exit(1); }
            if (herm(v, v) != 1) continue;
            if (keyof(v) < MINK) continue;
            U[i] = v;
            if (partial_ok(U, i)) found = 1;
        }
        if (!found) return 0;
    }
    for (int j = 0; j < 7; j++) if (keyof(column(U, j)) < MINK) return 0;
    return 1;
}
/* row permutation: new row g[i] = old row i */
static void permrows(uint32_t *U, const int *g) { uint32_t V[7]; for (int i = 0; i < 7; i++) V[g[i]] = U[i]; memcpy(U, V, sizeof V); }
static void apply_all(uint32_t *U, const gelem *e) { for (int i = 0; i < 7; i++) U[i] = gapply(e, U[i]); }

static int canonicalize(uint32_t *U) {
    int minr = 99, minc = 99;
    for (int i = 0; i < 7; i++) { int kr = keyof(U[i]), kc = keyof(column(U, i)); if (kr < 0 || kc < 0) return -1; if (kr < minr) minr = kr; if (kc < minc) minc = kc; }
    if (minc < minr) {   /* conjugate transpose */
        uint32_t V[7];
        for (int i = 0; i < 7; i++) { uint32_t c = column(U, i), w = 0; for (int j = 0; j < 7; j++) w |= (uint32_t)CONJ[vget(c, j)] << (4 * j); V[i] = w; }
        memcpy(U, V, sizeof V); minr = minc;
    }
    int i0 = -1; for (int i = 0; i < 7; i++) if (keyof(U[i]) == minr) { i0 = i; break; }
    for (int g = 0; g < 168; g++) if (AUT[g][i0] == 0) { permrows(U, AUT[g]); break; }
    uint32_t r = orbit_rep_vector(minr);
    int done = 0;
    for (int g = 0; g < 168 && !done; g++) for (int f = 0; f < 4 && !done; f++) {
        uint32_t w = U[0]; for (int k = 0; k < f; k++) w = frob(w);
        w = vperm(w, AUT[g]);
        if (npat(w) != npat(r)) continue;
        gelem e; for (int i = 0; i < 7; i++) e.perm[i] = AUT[g][i];
        e.f = f; for (int i = 0; i < 7; i++) e.D[i] = vget(r, i) ? MUL[vget(r, i)][INV[vget(w, i)]] : 1;
        apply_all(U, &e); done = 1;
    }
    if (!done || U[0] != r) { fprintf(stderr, "could not map row 0 to rep\n"); exit(1); }
    build_stab(r);
    int i1 = -1; uint32_t best = 0xFFFFFFFFu;
    for (int i = 1; i < 7; i++) { uint32_t k = key2of(U[i]); if (k < best) { best = k; i1 = i; } }
    for (int g = 0; g < 168; g++) if (AUT[g][0] == 0 && AUT[g][i1] == 1) { permrows(U, AUT[g]); break; }
    /* apply an element of Stab(r) (incl. free scalings of zero positions) taking row 1 to key2 */
    int zp[7], nz = 0; for (int i = 0; i < 7; i++) if ((ZNIB >> (4 * i)) & 1) zp[nz++] = i;
    int ncomb = 1; for (int k = 0; k < nz; k++) ncomb *= 5;
    done = 0;
    for (int s = 0; s < NSTAB && !done; s++) for (int comb = 0; comb < ncomb && !done; comb++) {
        gelem e = STAB[s]; int cc = comb;
        for (int k = 0; k < nz; k++) { e.D[zp[k]] = MU5[cc % 5]; cc /= 5; }
        if (gapply(&e, r) != r) { fprintf(stderr, "bad stab elt\n"); exit(1); }
        if (minrep(gapply(&e, U[1])) == best) { apply_all(U, &e); done = 1; }
    }
    if (!done) { fprintf(stderr, "no stab element reaches key2\n"); exit(1); }
    for (int i = 1; i < 7; i++) U[i] = minrep(U[i]);
    if (U[1] != best) { fprintf(stderr, "row 1 != key2\n"); exit(1); }
    /* (C5): minimal key2 among positions 2,4,5,6 goes to position 2 */
    static const int P4[4] = {2, 4, 5, 6};
    int i2 = -1; best = 0xFFFFFFFFu;
    for (int t = 0; t < 4; t++) { uint32_t k = key2of(U[P4[t]]); if (k < best) { best = k; i2 = P4[t]; } }
    for (int g = 0; g < 168; g++) if (AUT[g][0] == 0 && AUT[g][1] == 1 && AUT[g][i2] == 2) { permrows(U, AUT[g]); break; }
    /* verify (C1)-(C5) */
    int k0 = keyof(U[0]);
    for (int i = 0; i < 7; i++) if (keyof(U[i]) < k0 || keyof(column(U, i)) < k0) { fprintf(stderr, "C1 fails\n"); exit(1); }
    if (U[0] != orbit_rep_vector(k0)) { fprintf(stderr, "C2 fails\n"); exit(1); }
    if (key2of(U[1]) != U[1]) { fprintf(stderr, "C3a fails\n"); exit(1); }
    for (int i = 2; i < 7; i++) if (key2of(U[i]) < U[1]) { fprintf(stderr, "C3b fails\n"); exit(1); }
    for (int i = 1; i < 7; i++) if (minrep(U[i]) != U[i]) { fprintf(stderr, "C4 fails\n"); exit(1); }
    for (int t = 1; t < 4; t++) if (key2of(U[P4[t]]) < key2of(U[2])) { fprintf(stderr, "C5 fails\n"); exit(1); }
    return k0;
}

int main(int argc, char **argv) {
    int thr = atoi(argv[1]), num = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL * (strtoull(argv[3], 0, 10) + 1);
    if (argc > 4) MINK = atoi(argv[4]);
    common_init(thr);
    printf("THR=%d NORB=%d\n", THR, NORB);
    int made = 0, attempts = 0;
    while (made < num) {
        uint32_t U[7];
        attempts++;
        if (!gen(U)) continue;
        if (!is_unitary(U) || !full_ok(U)) { fprintf(stderr, "generated matrix fails verification!\n"); return 1; }
        uint32_t C[7]; memcpy(C, U, sizeof C);
        int k0 = canonicalize(C);
        if (k0 < 0) { fprintf(stderr, "row/col not in R?\n"); return 1; }
        if (!is_unitary(C) || !full_ok(C)) { fprintf(stderr, "canonical form fails verification!\n"); return 1; }
        printf("PLANT %d attempts=%d orig:", made, attempts);
        for (int i = 0; i < 7; i++) printf(" %07x", U[i]);
        printf("\nCANON %d K0=%d node1=%07x guide(pos3,pos2)=%07x,%07x matrix:", made, k0, C[1], C[3], C[2]);
        for (int i = 0; i < 7; i++) printf(" %07x", C[i]);
        printf("\n"); fflush(stdout);
        made++;
    }
    return 0;
}
