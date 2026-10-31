/* stab.h -- H0 = { v -> D * perm(frob^f(v)) } (D diagonal over mu5, perm in GL(3,2), f mod 4);
 * exact stabiliser of a row r in H0, and key2(u) = min over g in Stab(r) of minrep(g u). */
#ifndef STAB_H
#define STAB_H
#include "common.h"
typedef struct { int8_t perm[7]; int8_t f; uint8_t D[7]; } gelem;
/* Stab(r) = { D_Z o g : g in STAB[], D_Z any mu5-scaling of the zero positions Z of r }.
   STAB[] lists one element per (perm, f) preserving the class pattern of r, with D = 1 on Z. */
static gelem STAB[168 * 4];
static int NSTAB;
static uint32_t ZNIB;                    /* nibble mask of the zero positions of r */

static inline uint32_t gapply(const gelem *g, uint32_t v) {
    for (int k = 0; k < g->f; k++) v = frob(v);
    uint32_t w = 0;
    for (int i = 0; i < 7; i++) w |= (uint32_t)MUL[g->D[(int)g->perm[i]]][vget(v, i)] << (4 * g->perm[i]);
    return w;
}
static void build_stab(uint32_t r) {
    NSTAB = 0; ZNIB = 0;
    int pr = npat(r);
    for (int i = 0; i < 7; i++) if (!vget(r, i)) ZNIB |= 15u << (4 * i);
    for (int g = 0; g < 168; g++) for (int f = 0; f < 4; f++) {
        uint32_t w = r; for (int k = 0; k < f; k++) w = frob(w);
        w = vperm(w, AUT[g]);
        if (npat(w) != pr) continue;
        gelem e;
        for (int i = 0; i < 7; i++) e.perm[i] = AUT[g][i];
        e.f = f;
        for (int i = 0; i < 7; i++) { int ri = vget(r, i), wi = vget(w, i); e.D[i] = ri ? MUL[ri][INV[wi]] : 1; }
        for (int i = 0; i < 7; i++) if (NRM[e.D[i]] != 1) { fprintf(stderr, "D not in mu5\n"); exit(1); }
        if (gapply(&e, r) != r) { fprintf(stderr, "stab element does not fix r\n"); exit(1); }
        STAB[NSTAB++] = e;
    }
}
/* min over zeta in mu5 and D_Z of the packed value of zeta * D_Z * w:
   Z-coordinates independently become the least element of their mu5-coset (= CLS_REP of their class),
   the remaining coordinates are minimised jointly over zeta (Z nibbles are equal for all zeta). */
static inline uint32_t canonZ(uint32_t w) {
    uint32_t ws = w & ~ZNIB, z = 0;
    if (ZNIB) for (int i = 0; i < 7; i++) if ((ZNIB >> (4 * i)) & 1) z |= (uint32_t)CLS_REP[NCLS[vget(w, i)]] << (4 * i);
    uint32_t best = ws;
    for (int k = 0; k < 5; k++) { uint32_t t = smul(MU5[k], ws); if (t < best) best = t; }
    return best | z;
}
static inline uint32_t key2of(uint32_t u) {
    uint32_t best = 0xFFFFFFFFu;
    for (int s = 0; s < NSTAB; s++) { uint32_t w = canonZ(gapply(&STAB[s], u)); if (w < best) best = w; }
    return best;
}
/* reference implementation: explicit enumeration of all D_Z and zeta (slow; for tests / canonicalisation) */
static uint32_t key2of_slow(uint32_t u) {
    int zp[7], nz = 0;
    for (int i = 0; i < 7; i++) if ((ZNIB >> (4 * i)) & 1) zp[nz++] = i;
    int ncomb = 1; for (int k = 0; k < nz; k++) ncomb *= 5;
    uint32_t best = 0xFFFFFFFFu;
    for (int s = 0; s < NSTAB; s++) {
        uint32_t w = gapply(&STAB[s], u);
        for (int comb = 0; comb < ncomb; comb++) {
            uint32_t x = w; int cc = comb;
            for (int k = 0; k < nz; k++) { x = vset(x, zp[k], MUL[MU5[cc % 5]][vget(x, zp[k])]); cc /= 5; }
            uint32_t m = minrep(x); if (m < best) best = m;
        }
    }
    return best;
}
#endif
