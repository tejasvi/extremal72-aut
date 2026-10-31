/* items.c -- report items 1-3 by direct enumeration (independent of the pattern shortcut where possible) */
#include "common.h"
#include <omp.h>
int main(int argc, char **argv) {
    int thr = argc > 1 ? atoi(argv[1]) : 16;
    common_init(thr);
    /* sanity: pair M values are position independent */
    for (int c0 = 1; c0 < 16; c0++) for (int c1 = 1; c1 < 16; c1++) {
        int ref = -1;
        for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) if (i != j) {
            uint32_t a = ((uint32_t)c0 << (4*i)) | ((uint32_t)c1 << (4*j));
            int m = Mvec(a); if (ref < 0) ref = m; else if (m != ref) { printf("pair M position dependent!\n"); return 1; }
        }
    }
    /* item 1 and 2 by brute force over all 2^28 vectors, using all 15 scalars */
    long long cntR = 0, cntIso = 0, cntUnit = 0;
    #pragma omp parallel for reduction(+:cntR,cntIso,cntUnit) schedule(dynamic, 1)
    for (uint32_t hi = 0; hi < (1u << 12); hi++) {
        for (uint32_t lo = 0; lo < (1u << 16); lo++) {
            uint32_t u = (hi << 16) | lo;
            if (!u) continue;
            int s = herm(u, u);
            if (s == 1) {
                cntUnit++;
                int ok = 1;
                for (int c = 1; c < 16 && ok; c++) if (Mvec(smul(c, u)) < thr - WTE[c]) ok = 0;
                cntR += ok;
            } else if (s == 0) {
                int ok = 1;
                for (int c = 1; c < 16 && ok; c++) if (Mvec(smul(c, u)) < thr) ok = 0;
                cntIso += ok;
            }
        }
    }
    long long patR = 0; int npR = 0;
    for (int p = 0; p < 16384; p++) if (ISR[p]) { long long v = 1; for (int k = 0; k < pnnz(p); k++) v *= 5; patR += v; npR++; }
    printf("THR=%d\n", thr);
    printf("unit vectors: %lld\n", cntUnit);
    printf("ITEM1 |R| (brute force) = %lld ; via %d class patterns = %lld\n", cntR, npR, patR);
    printf("ITEM2 isotropic v!=0 with M(cv)>=THR for all c: %lld\n", cntIso);
    printf("orbits of R under H0: %d\n", NORB);
    for (int k = 0; k < NORB; k++) {
        int p = ORB_REP[k]; uint32_t r = orbit_rep_vector(k);
        printf("  key %d: rep pattern 0x%04x weights (", k, p);
        for (int i = 0; i < 7; i++) printf("%d%s", CLSWT[(p >> (2*i)) & 3], i < 6 ? "," : ")");
        printf(" classes (");
        for (int i = 0; i < 7; i++) printf("%d%s", (p >> (2*i)) & 3, i < 6 ? "," : ")");
        printf(" rep vector 0x%07x  #patterns %d  #vectors %lld\n", r, ORB_NPAT[k], ORB_NVEC[k]);
    }
    /* item 3: for each orbit rep r, number of u in R with <r,u>=0 and (*) on all a supported on {0,1} */
    for (int k = 0; k < NORB; k++) {
        uint32_t r = orbit_rep_vector(k);
        if (keyof(r) != k) { printf("rep key mismatch\n"); return 1; }
        uint32_t rm[16]; for (int c = 0; c < 16; c++) rm[c] = smul(c, r);
        int Ma[16][16];
        for (int c0 = 0; c0 < 16; c0++) for (int c1 = 0; c1 < 16; c1++) Ma[c0][c1] = Mvec((uint32_t)c0 | ((uint32_t)c1 << 4));
        long long cnt = 0;
        #pragma omp parallel for reduction(+:cnt) schedule(dynamic, 1)
        for (uint32_t hi = 0; hi < (1u << 12); hi++) {
            for (uint32_t lo = 0; lo < (1u << 16); lo++) {
                uint32_t u = (hi << 16) | lo;
                if (herm(r, u) != 0 || herm(u, u) != 1) continue;
                int ok = 1;
                for (int c1 = 1; c1 < 16 && ok; c1++) {
                    uint32_t m1 = smul(c1, u);
                    for (int c0 = 0; c0 < 16; c0++) if (Ma[c0][c1] + Mvec(rm[c0] ^ m1) < thr) { ok = 0; break; }
                }
                cnt += ok;
            }
        }
        printf("ITEM3 key %d rep 0x%07x: valid second rows = %lld (= %lld up to row scaling by mu5)\n", k, r, cnt, cnt / 5);
        fflush(stdout);
    }
    return 0;
}
