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
#include "nauty.h"
#include "nausparse.h"
#include <math.h>

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
static uint64_t Tb[192];            /* Tb[b]: bit (2*kk+s) set iff pair-bit b is in U_s[kk] */
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
static uint8_t v3[495];
static int16_t idx4_12[4096];       /* 12-bit 4-subset pattern -> index in pat4_12 */
static long nsplit, nsplitpass;
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
/* ---- L1-level tables (T, A fixed for all children of an L1 node) ---- */
static int opts[16], oidx[24]; static uint32_t O1c;
static uint16_t Lk[36][120][16];       /* link of pair sigma (index) in F(Y4): rows over o-indices */
static int pairidx[16][16];
static uint16_t zpat16[1820];
static uint8_t fTz[1820], fAz[1820];
static int16_t zidx16[65536];
static int use_L1 = 1;
static void build_L1_tables(uint32_t O1, uint32_t T, uint32_t A) {
    O1c = FULL24 & ~O1;
    int k = 0; for (uint32_t m = O1c; m; m &= m - 1) { opts[k] = __builtin_ctz(m); oidx[opts[k]] = k; k++; }
    uint32_t cols[2] = { T, A };
    for (int i = 0; i < 2; i++) {
        uint32_t m = cols[i]; int j = 0;
        for (; m; m &= m - 1) cpt[i][j++] = 1u << __builtin_ctz(m);
        for (int kq = 0; kq < 3; kq++) { cref[i][kq] = cpt[i][0] | cpt[i][kq + 1]; ccmp[i][kq] = cols[i] ^ cref[i][kq]; }
    }
    memset(Lk, 0, sizeof Lk);
    for (int z = 0; z < 1820; z++) {
        uint32_t Z = _pdep_u32(zpat16[z], O1c);
        fTz[z] = F8(T | Z); fAz[z] = F8(A | Z);
        int zz[4], j = 0; for (uint32_t m = zpat16[z]; m; m &= m - 1) zz[j++] = __builtin_ctz(m);
        for (int y = 0; y < 36; y++) {
            uint32_t Y4 = colpair(0, y / 6) | colpair(1, y % 6);
            if (!F8(Y4 | Z)) continue;
            /* the 3 splits of Z into two pairs, both orientations */
            static const int sp[3][4] = { {0,1,2,3}, {0,2,1,3}, {0,3,1,2} };
            for (int t = 0; t < 3; t++) {
                int a = zz[sp[t][0]], b = zz[sp[t][1]], c = zz[sp[t][2]], d2 = zz[sp[t][3]];
                uint16_t *r1 = Lk[y][pairidx[a][b]], *r2 = Lk[y][pairidx[c][d2]];
                r1[c] |= (uint16_t)(1u << d2); r1[d2] |= (uint16_t)(1u << c);
                r2[a] |= (uint16_t)(1u << b); r2[b] |= (uint16_t)(1u << a);
            }
        }
    }
}
static void build_L2_tables(uint32_t T, uint32_t A, uint32_t B) {
    uint32_t cols[3] = { T, A, B };
    for (int i = 0; i < 3; i++) {
        uint32_t m = cols[i]; int j = 0;
        for (; m; m &= m - 1) cpt[i][j++] = 1u << __builtin_ctz(m);
        for (int k = 0; k < 3; k++) { cref[i][k] = cpt[i][0] | cpt[i][k + 1]; ccmp[i][k] = cols[i] ^ cref[i][k]; }
    }
    if (use_L1 && !debugfp) {
        uint32_t X16 = 0; for (int i = 0; i < 12; i++) X16 |= 1u << oidx[xpts[i]];
        int pib[6];
        for (int qB = 0; qB < 6; qB++) { uint32_t pb = colpair(2, qB); pib[qB] = pairidx[oidx[__builtin_ctz(pb)]][oidx[31 - __builtin_clz(pb)]]; }
        int xo[12]; for (int i = 0; i < 12; i++) xo[i] = oidx[xpts[i]];
        for (int kT = 0; kT < 3; kT++) for (int kA = 0; kA < 3; kA++) for (int kB = 0; kB < 3; kB++) {
            int kk = (kT * 3 + kA) * 3 + kB;
            for (int sgn = 0; sgn < 2; sgn++) {
                uint16_t acc[16]; memset(acc, 0, sizeof acc);
                for (int e = 0; e < 8; e++) {
                    if ((__builtin_popcount(e) & 1) != sgn) continue;
                    int y = (2 * kT + (e & 1)) * 6 + (2 * kA + ((e >> 1) & 1));
                    const uint16_t *rows = Lk[y][pib[2 * kB + ((e >> 2) & 1)]];
                    for (int r = 0; r < 16; r++) acc[r] |= rows[r];
                }
                uint64_t w[3] = { 0, 0, 0 };
                for (int i = 0; i < 12; i++) { uint64_t r = _pext_u32(acc[xo[i]], X16); int bit = i * 16; w[bit >> 6] |= r << (bit & 63); }
                Uw[kk][sgn][0] = w[0]; Uw[kk][sgn][1] = w[1]; Uw[kk][sgn][2] = w[2];
            }
        }
        goto build_Tb;
    }
    if (use_L1) {
        uint32_t X16 = 0; for (int i = 0; i < 12; i++) X16 |= 1u << oidx[xpts[i]];
        for (int qB = 0; qB < 6; qB++) {
            uint32_t pb = colpair(2, qB); int b0 = oidx[__builtin_ctz(pb)], b1 = oidx[31 - __builtin_clz(pb)];
            int pi = pairidx[b0][b1];
            for (int y = 0; y < 36; y++) {
                const uint16_t *rows = Lk[y][pi];
                uint64_t w[3] = { 0, 0, 0 };
                for (int i = 0; i < 12; i++) {
                    uint64_t r = _pext_u32(rows[oidx[xpts[i]]], X16);
                    int bit = i * 16; w[bit >> 6] |= r << (bit & 63);
                }
                int id = (y / 6) * 36 + (y % 6) * 6 + qB;
                FPw[id][0] = w[0]; FPw[id][1] = w[1]; FPw[id][2] = w[2];
                if (debugfp) { uint64_t r2[3]; fp_lookup(colpair(0, y / 6) | colpair(1, y % 6) | pb, r2); if (memcmp(r2, FPw[id], 24)) nFPdiff++; }
            }
        }
    } else
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
build_Tb:
    memset(Tb, 0, sizeof Tb);
    for (int kk = 0; kk < 27; kk++) for (int s = 0; s < 2; s++) for (int r = 0; r < 3; r++) {
        uint64_t w = Uw[kk][s][r];
        while (w) { int b = __builtin_ctzll(w); w &= w - 1; Tb[r * 64 + b] |= 1ULL << (2 * kk + s); }
    }
}
static int cc[4];
static uint32_t coset_rep4(const int *k, int p, uint32_t C) {
    uint32_t O = cref[0][k[0]] | cref[1][k[1]] | cref[2][k[2]];
    uint32_t c0 = 1u << xpts[cc[0]], ck = 1u << xpts[cc[k[3] + 1]];
    uint32_t ref = c0 | ck;
    return O | (p ? (C ^ ref) : ref);
}
static uint64_t vp[3][2];
#define EVEN54 0x0015555555555555ULL
static void precompute_C_bits(void) {
    for (int k = 0; k < 3; k++) {
        int a = -1, b = -1;
        for (int t = 1; t < 4; t++) if (t != k + 1) { if (a < 0) a = cc[t]; else b = cc[t]; }
        uint64_t R = Tb[cc[0] * 16 + cc[k + 1]], Cm = Tb[a * 16 + b];
        vp[k][0] = ~((R & EVEN54) | ((Cm >> 1) & EVEN54)) & EVEN54;
        vp[k][1] = ~((Cm & EVEN54) | ((R >> 1) & EVEN54)) & EVEN54;
    }
}
static uint32_t E1[3][2], E2[3][2], E3[3][2];
static const uint64_t PM0 = 0x15555ULL, PM1 = 0x15555ULL << 18, PM2 = 0x15555ULL << 36;
static inline void make_E(void) {
    for (int k = 0; k < 3; k++) for (int p = 0; p < 2; p++) {
        E1[k][p] = (uint32_t)_pext_u64(vp[k][p], PM0);
        E2[k][p] = (uint32_t)_pext_u64(vp[k][p], PM1);
        E3[k][p] = (uint32_t)_pext_u64(vp[k][p], PM2);
    }
}
/* fast existence of a valid A-structure: c1 (kT=0), c2 (kT=1), c3 (kT=2) with distinct partitions per column */
static int atest_fast(void) {
    precompute_C_bits(); make_E();
    for (int kC1 = 0; kC1 < 3; kC1++) for (int p1 = 0; p1 < 2; p1++) {
        uint32_t s1 = E1[kC1][p1]; if (!s1) continue;
        for (int kC2 = 0; kC2 < 3; kC2++) { if (kC2 == kC1) continue; int kC3 = 3 - kC1 - kC2;
            for (int p2 = 0; p2 < 2; p2++) {
                uint32_t s2 = E2[kC2][p2]; if (!s2) continue;
                uint32_t s3 = E3[kC3][p1 ^ p2]; if (!s3) continue;
                for (uint32_t t1 = s1; t1; t1 &= t1 - 1) { int i1 = __builtin_ctz(t1), a1 = i1 / 3, b1 = i1 % 3;
                    for (uint32_t t2 = s2; t2; t2 &= t2 - 1) { int i2 = __builtin_ctz(t2), a2 = i2 / 3, b2 = i2 % 3;
                        if (a2 == a1 || b2 == b1) continue;
                        int a3 = 3 - a1 - a2, b3 = 3 - b1 - b2;
                        if ((s3 >> (a3 * 3 + b3)) & 1) return 1;
                    }
                }
            }
        }
    }
    return 0;
}
static uint8_t cb6[27];
static void precompute_C_bits_old(void) {
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
#define CV(kT, kA, kB, kC, p) ((vp[kC][p] >> (2 * (((kT) * 3 + (kA)) * 3 + (kB)))) & 1)
static double tAT, tEXT, tV3, tFP;
static int atest_exists(void) {
    precompute_C_bits();
    int k1[4], k2[4], k3[4];
    k1[0] = 0; k2[0] = 1; k3[0] = 2;
    for (k1[1] = 0; k1[1] < 3; k1[1]++) for (k1[2] = 0; k1[2] < 3; k1[2]++) for (k1[3] = 0; k1[3] < 3; k1[3]++)
    for (int p1 = 0; p1 < 2; p1++) {
        if (!CV(k1[0], k1[1], k1[2], k1[3], p1)) continue;
        for (int m = 0; m < 8; m++) {
            for (int i = 1; i < 4; i++) { int o0 = (k1[i] + 1) % 3, o1 = (k1[i] + 2) % 3; k2[i] = ((m >> (i - 1)) & 1) ? o1 : o0; k3[i] = 3 - k1[i] - k2[i]; }
            for (int p2 = 0; p2 < 2; p2++) {
                if (!CV(k2[0], k2[1], k2[2], k2[3], p2)) continue;
                if (CV(k3[0], k3[1], k3[2], k3[3], p1 ^ p2)) return 1;
            }
        }
    }
    return 0;
}
static int split_ok(uint32_t Cpat) {
    /* is there a split of X \ C into D u E (both valid 4-sets) with A-tests passing for D and E? */
    uint32_t Rpat = 0xFFF & ~Cpat;
    int save[4]; memcpy(save, cc, sizeof save);
    int lo = __builtin_ctz(Rpat); int ok = 0;
    uint32_t rest = Rpat & ~(1u << lo);
    /* D = {lo} + 3 of rest (7 points): 35 choices */
    for (uint32_t t = 0; t < 128 && !ok; t++) if (__builtin_popcount(t) == 3) {
        uint32_t Dp = (1u << lo) | _pdep_u32(t, rest), Ep = Rpat & ~Dp;
        if (!v3[idx4_12[Dp]] || !v3[idx4_12[Ep]]) continue;
        nsplit++;
        int j = 0; for (uint32_t c = Dp; c; c &= c - 1) cc[j++] = __builtin_ctz(c);
        if (!atest_fast()) continue;
        j = 0; for (uint32_t c = Ep; c; c &= c - 1) cc[j++] = __builtin_ctz(c);
        if (!atest_fast()) continue;
        nsplitpass++; ok = 1;
    }
    memcpy(cc, save, sizeof save);
    precompute_C_bits();
    return ok;
}
static uint32_t curCpat;
static void atest(uint32_t T, uint32_t A, uint32_t B, uint32_t C) {
    nK4++;
    if (!atest_fast()) return;
    precompute_C_bits();
    int splitchecked = 0;
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
                if (!splitchecked) { splitchecked = 1; if (!split_ok(curCpat)) return; }
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
    int cnt[12] = { 0 }, nv = 0;
    for (int i = 0; i < 495; i++) {
        uint32_t C = _pdep_u32(pat4_12[i], Xmask);
        if (use_L1) { int zi = zidx16[_pext_u32(C, O1c)]; v3[i] = !fTz[zi] && !fAz[zi] && !F8(B | C) && !F8(Xmask & ~C); }
        else v3[i] = !F8(T | C) && !F8(A | C) && !F8(B | C) && !F8(Xmask & ~C);
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
        curCpat = pat4_12[i];
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
    if (use_L1) { uint32_t T = keep[0] & O1; double tq = now(); build_L1_tables(O1, T, O1 & ~T); tFP += now() - tq; }
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
    if (exhaustive || !E_n10 || getenv("ROOTEX")) {
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
/* ---- symmetry reduction at L1: orbits of Stab_{Aut_Mon(E)}(F0) (coordinate permutations) on octads through F0 ---- */
static int use_sym = 0; static int l1rep[969]; static long nl1orb;
static int (*sgen)[24]; static int nsgen;
static void sym_cb(int count, int *perm, int *orbits, int numorbits, int stabvertex, int n) {
    sgen = realloc(sgen, sizeof(int[24]) * (nsgen + 1));
    for (int i = 0; i < 24; i++) sgen[nsgen][i] = perm[3 * i] / 3;
    nsgen++;
}
typedef struct { f4v *w; int n, cap; } wl3_t;
static void wcb3(f4v x, int nr, void *c) { wl3_t *L = (wl3_t *)c; if (f4wt(x) != 8) return; if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 4096; L->w = realloc(L->w, sizeof(f4v) * L->cap); } L->w[L->n++] = x; }
static const f4v *curgen;
static int uf9[969];
static int uf9f(int x) { while (uf9[x] != x) { uf9[x] = uf9[uf9[x]]; x = uf9[x]; } return x; }
static void compute_l1_orbits(uint32_t F0) {
    for (int i = 0; i < 969; i++) uf9[i] = i;
    nsgen = 0;
    wl3_t L = { 0, 0, 0 };
    sd_lowwords(curgen, 24, 8, wcb3, &L);
    { f4v R[16]; int r = 0; for (int j = 0; j < L.n && r < 12; j++) { R[r] = L.w[j]; if (f4rank(R, r + 1, 24) == r + 1) r++; }
      if (r < 12) { /* weight-8 words do not span E: their automorphisms need not preserve E -> no reduction */
          free(L.w); nl1orb = 0; for (int i = 0; i < 969; i++) l1rep[i] = 1; return; } }
    int n = 24, nw = L.n, nv = 3 * n + nw;
    size_t ne = 3 * n + 2 * 8 * (size_t)nw;
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "sym"); sg.nv = nv; sg.nde = ne;
    int *deg = calloc(nv, sizeof(int));
    for (int i = 0; i < 3 * n; i++) deg[i] = 1;
    for (int j = 0; j < nw; j++) { deg[3 * n + j] = 8; for (uint32_t m = f4supp(L.w[j]); m; m &= m - 1) { int i = __builtin_ctz(m); int e = f4get(L.w[j], i); deg[3 * i + (e == 1 ? 0 : e == 2 ? 1 : 2)]++; } }
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg.v[v] = pos; sg.d[v] = 0; pos += deg[v]; }
    for (int i = 0; i < n; i++) for (int a = 0; a < 3; a++) { int v = 3 * i + a; sg.e[sg.v[v] + sg.d[v]++] = 3 * i + (a + 1) % 3; }
    for (int j = 0; j < nw; j++) { int y = 3 * n + j; for (uint32_t m = f4supp(L.w[j]); m; m &= m - 1) { int i = __builtin_ctz(m), e = f4get(L.w[j], i), x = 3 * i + (e == 1 ? 0 : e == 2 ? 1 : 2); sg.e[sg.v[y] + sg.d[y]++] = x; sg.e[sg.v[x] + sg.d[x]++] = y; } }
    free(deg);
    int *lab = malloc(sizeof(int) * nv), *ptn = malloc(sizeof(int) * nv), *orb = malloc(sizeof(int) * nv);
    int q = 0;
    for (int i = 0; i < n; i++) if ((F0 >> i) & 1) for (int a = 0; a < 3; a++) { lab[q] = 3 * i + a; ptn[q] = 1; q++; }
    ptn[q - 1] = 0;
    for (int i = 0; i < n; i++) if (!((F0 >> i) & 1)) for (int a = 0; a < 3; a++) { lab[q] = 3 * i + a; ptn[q] = 1; q++; }
    ptn[q - 1] = 0;
    for (int j = 0; j < nw; j++) { lab[q] = 3 * n + j; ptn[q] = 1; q++; }
    ptn[q - 1] = 0;
    DEFAULTOPTIONS_SPARSEDIGRAPH(opt);
    opt.getcanon = FALSE; opt.defaultptn = FALSE; opt.userautomproc = sym_cb;
    statsblk st;
    sparsenauty(&sg, lab, ptn, orb, &opt, &st, NULL);
    free(lab); free(ptn); free(orb); free(L.w); SG_FREE(sg);
    /* union-find over the 969 candidate octads through F0 */
    uint32_t comp = FULL24 & ~F0;
    static int idx3[1 << 19]; static int init3 = 0;
    if (!init3) { for (int i = 0; i < 969; i++) idx3[pat3_19[i]] = i; init3 = 1; }
    for (int g = 0; g < nsgen; g++) for (int i = 0; i < 969; i++) {
        uint32_t O = F0 | _pdep_u32(pat3_19[i], comp), img = 0;
        for (uint32_t m = O; m; m &= m - 1) img |= 1u << sgen[g][__builtin_ctz(m)];
        if ((img & F0) != F0) { fprintf(stderr, "stabilizer generator does not fix F0\n"); exit(1); }
        int j = idx3[_pext_u32(img, comp)];
        int a = uf9f(i), b = uf9f(j); if (a != b) uf9[a] = b;
    }
    nl1orb = 0;
    for (int i = 0; i < 969; i++) { l1rep[i] = (uf9f(i) == i); }
    for (int i = 0; i < 969; i++) if (l1rep[i] && !F8(F0 | _pdep_u32(pat3_19[i], comp))) nl1orb++;
}
static long nroot;
static void run_test(int exhaustive_root) {
    memset(nodes, 0, sizeof nodes); memset(nL, 0, sizeof nL); nK4 = nApass = nFPdiff = 0; nsplit = nsplitpass = 0; tAT = tEXT = tV3 = tFP = 0; nsol = nchk = 0; nsolstore = 0; solhash = 0;
    resetK(); tStart = now();
    int rc; uint32_t F0 = choose_root(&rc, exhaustive_root);
    nroot = rc;
    uint32_t comp = FULL24 & ~F0;
    if (use_sym) compute_l1_orbits(F0);
    for (int i = 0; i < 969; i++) {
        uint32_t O1 = F0 | _pdep_u32(pat3_19[i], comp);
        if (F8(O1)) continue;
        if (use_sym && !l1rep[i]) continue;
        uint32_t buf[4];
        nL[1]++;
        int m = addK(O1, buf);
        level2(O1);
        undoK(buf, m);
        if (getenv("PROG") && (nL[1] % 10 == 0)) { fprintf(stderr, "  L1 %ld/%ld L2=%ld K4=%ld t=%.1f\n", nL[1], nroot, nL[2], nK4, now() - tStart); }
    }
}
static void report(const char *tag, double dt) {
    printf("%s root=%ld%s L1=%ld L2=%ld K4=%ld Apass=%ld split=%ld/%ld ext:", tag, nroot, use_sym ? "(sym)" : "", nL[1], nL[2], nK4, nApass, nsplitpass, nsplit);
    for (int d = 7; d < 12; d++) printf(" %ld", nodes[d]);
    printf(" sols=%ld hash=%016llx chk=%ld%s tV3=%.2f tFP=%.2f tAT=%.2f tEXT=%.2f t=%.2fs\n", nsol, (unsigned long long)solhash, nchk, debugfp ? (nFPdiff ? " FPDIFF!" : " fpok") : "", tV3, tFP, tAT - tEXT, tEXT, dt);
    fflush(stdout);
}
int main(int argc, char **argv) {
    gcore_init();
    { int k = 0; for (uint32_t p = 0; p < 4096; p++) if (__builtin_popcount(p) == 4) { idx4_12[p] = k; pat4_12[k++] = p; } }
    init_closures();
    { int k = 0; for (uint32_t p = 0; p < 65536; p++) if (__builtin_popcount(p) == 4) { zidx16[p] = k; zpat16[k++] = p; } }
    { int k = 0; for (int i = 0; i < 16; i++) for (int j = i + 1; j < 16; j++) { pairidx[i][j] = pairidx[j][i] = k++; } }
    if (getenv("NOL1")) use_L1 = 0;
    { int k = 0; for (uint32_t p = 0; p < (1u << 24); p++) if (__builtin_popcount(p) == 5) all5[k++] = p; }
    if (getenv("MAXSCAN")) maxscan = atoi(getenv("MAXSCAN"));
    if (getenv("SAMPLE2")) sample2 = atoi(getenv("SAMPLE2"));
    if (getenv("DEBUGFP")) debugfp = 1;
    char mode = argv[1][0];
    if (mode == 'R') {
        /* R file slice nslices startidx : test codes with index % nslices == slice and index >= startidx */
        FILE *f = fopen(argv[2], "r"); long slice = atol(argv[3]), nsl = atol(argv[4]), start = argc > 5 ? atol(argv[5]) : 0;
        long endidx = argc > 6 ? atol(argv[6]) : (1L << 62);
        char line[8192]; long ci = 0, ndone = 0; double tsum = 0; long totsol = 0;
        use_incidence = 1;
        while (fgets(line, sizeof line, f)) {
            long my = ci++;
            if (my >= endidx) break;
            if (my % nsl != slice || my < start) continue;
            f4v gen[12]; if (!parse_code_line(line, gen)) { printf("BADLINE %ld\n", my); continue; }
            double autv = 0; if (strlen(line) > 193) autv = atof(line + 193);
            use_sym = (autv > 3.5) || getenv("SYM"); curgen = gen;
            double t0 = now();
            set_forbidden_from_E(gen);
            build_indexes();
            run_test(0);
            double dt = now() - t0; tsum += dt; ndone++; totsol += nsol;
            if (nsol) {
                printf("SOLUTION code %ld sols=%ld :", my, nsol);
                for (int s2 = 0; s2 < nsolstore; s2++) { printf(" G"); for (int i = 0; i < 12; i++) printf(" %06x", solbasis[s2][i]); }
                printf(" E %s", line); fflush(stdout);
            }
            if (ndone % 200 == 0) { printf("progress slice %ld: done %ld last %ld avg %.2fs sols %ld\n", slice, ndone, my, tsum / ndone, totsol); fflush(stdout); }
        }
        printf("FINISHED slice %ld: done %ld avg %.2fs total solutions %ld\n", slice, ndone, ndone ? tsum / ndone : 0, totsol);
        return 0;
    }
    if (mode == 'Q') {
        /* planted on a real code: Q file codeindex seed : forbidden tables of a real code, then the 759 octads and
           2576 dodecads of a random relabelled Golay code G* are made allowed; the test must find G* */
        FILE *f = fopen(argv[2], "r"); long want = atol(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
        char line[8192]; long ci = 0; f4v gen[12]; int got = 0;
        while (fgets(line, sizeof line, f)) { if (ci++ == want) { got = parse_code_line(line, gen); break; } }
        if (!got) { fprintf(stderr, "no code %ld\n", want); return 1; }
        use_incidence = 1; use_sym = 0; curgen = gen;
        long nf = set_forbidden_from_E(gen);
        build_indexes();
        rng_t R; rng_seed(&R, seed);
        uint32_t W[4096]; golay_words(W);
        int p[24]; for (int i = 0; i < 24; i++) p[i] = i;
        for (int i = 23; i > 0; i--) { int j = rng_next(&R) % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
        uint8_t *keep = calloc(1 << 21, 1); long cleared8 = 0, cleared12 = 0;
        for (int m = 0; m < 4096; m++) {
            uint32_t w = applyperm(p, W[m]); SETB(keep, w);
            int c = __builtin_popcount(w);
            if (c == 8 && F8(w)) { CLRB(forb8, srank(w)); cleared8++; }
            if (c == 12 && F12(w)) { CLRB(forb12, srank(w)); cleared12++; }
        }
        double t1 = now();
        run_test(0);
        int found = 0;
        for (int s2 = 0; s2 < nsolstore; s2++) { int ok = 1; for (int i = 0; i < 12; i++) if (!GETB(keep, solbasis[s2][i])) ok = 0; found |= ok; }
        char tag[256]; snprintf(tag, sizeof tag, "plantedQ code %ld seed %lu cleared8=%ld cleared12=%ld forb8=%.3f found=%d", want, (unsigned long)seed, cleared8, cleared12, nf / 735471.0, found);
        report(tag, now() - t1);
        return 0;
    }
    if (mode == 'E') {
        FILE *f = fopen(argv[2], "r"); long maxc = argc > 3 ? atol(argv[3]) : 1L << 40; long first = argc > 4 ? atol(argv[4]) : 0;
        char line[8192]; long ci = 0;
        use_incidence = getenv("LOOKUPFP") ? 0 : 1;
        while (ci < first + maxc && fgets(line, sizeof line, f)) {
            if (ci++ < first) continue;
            f4v gen[12]; if (!parse_code_line(line, gen)) continue;
            use_sym = getenv("SYM") != NULL; curgen = gen;
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
