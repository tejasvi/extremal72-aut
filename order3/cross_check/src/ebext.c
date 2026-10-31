/* ebext.c -- own extension counts for the exact level chain of the E_B classification (C3 audit).
   For each class line "k KEY AUT[x2] GEN" (length NB): nv = number of nonzero cosets x + D in D^perp
   (Hermitian dual) that are isotropic (wt(x) even) and have minimum weight >= 8.
   output: aut sc nv */
#include "f4a.h"
static int NB;
int main(int argc, char **argv) {
    NB = atoi(argv[1]);
    FILE *f = fopen(argv[2], "r"); static char line[8192];
    while (fgets(line, sizeof line, f)) {
        int k; char key[512], autf[64], gen[512];
        if (sscanf(line, "%d %511s %63s %511s", &k, key, autf, gen) != 4) { printf("PARSEERR\n"); continue; }
        v24 D[8]; if (!parse_rows_B(gen, D, k)) { printf("PARSEERR2\n"); continue; }
        /* Hermitian dual = Euclidean dual of conj(D) */
        v24 c[8]; for (int t = 0; t < k; t++) c[t] = vconj(D[t]);
        int ord[32]; for (int i = 0; i < NB; i++) ord[i] = i;
        int piv[8]; int r = f4_rref(c, k, ord, NB, piv);
        if (r != k) { printf("RANKERR\n"); continue; }
        uint32_t pm = 0; for (int t = 0; t < k; t++) pm |= 1u << piv[t];
        v24 du[32]; int nd = 0;
        for (int fcol = 0; fcol < NB; fcol++) if (!((pm >> fcol) & 1)) {
            v24 x = { 0, 0 };
            x.a |= 1u << fcol;
            for (int t = 0; t < k; t++) { int s = vget(c[t], fcol); if (s) { if (s & 1) x.a |= 1u << piv[t]; if (s & 2) x.b |= 1u << piv[t]; } }
            du[nd++] = x;
        }
        /* check duals and self-orthogonality */
        int bad = 0;
        for (int i = 0; i < nd; i++) for (int t = 0; t < k; t++) if (vherm(du[i], D[t])) bad = 1;
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (vherm(D[i], D[j])) bad = 1;
        if (bad || nd != NB - k) { printf("DUALERR\n"); continue; }
        /* complement of D in D^perp: greedily extend a basis of D by dual vectors */
        v24 B[32]; int nb = 0, pvb[32];
        v24 comp[32]; int nc = 0;
        for (int t = 0; t < k; t++) {      /* insert D */
            v24 y = D[t];
            for (int q = 0; q < nb; q++) { int s = vget(y, pvb[q]); if (s) y = vadd(y, vscal(B[q], s)); }
            int cc = __builtin_ctz(vsupp(y)); y = vscal(y, F4INV[vget(y, cc)]);
            for (int q = 0; q < nb; q++) { int s = vget(B[q], cc); if (s) B[q] = vadd(B[q], vscal(y, s)); }
            B[nb] = y; pvb[nb++] = cc;
        }
        for (int i = 0; i < nd; i++) {
            v24 y = du[i];
            for (int q = 0; q < nb; q++) { int s = vget(y, pvb[q]); if (s) y = vadd(y, vscal(B[q], s)); }
            if (viszero(y)) continue;
            comp[nc++] = du[i];
            int cc = __builtin_ctz(vsupp(y)); y = vscal(y, F4INV[vget(y, cc)]);
            for (int q = 0; q < nb; q++) { int s = vget(B[q], cc); if (s) B[q] = vadd(B[q], vscal(y, s)); }
            B[nb] = y; pvb[nb++] = cc;
        }
        if (nc != NB - 2 * k) { printf("COMPERR %d\n", nc); continue; }
        /* all elements of D */
        int nD = 1; for (int t = 0; t < k; t++) nD *= 4;
        v24 *Dw = malloc(sizeof(v24) * (size_t)nD);
        for (int m = 0; m < nD; m++) { v24 x = { 0, 0 }; int mm = m; for (int t = 0; t < k; t++) { int s = mm & 3; mm >>= 2; if (s) x = vadd(x, vscal(D[t], s)); } Dw[m] = x; }
        long long nv = 0; long long ncos = 1; for (int t = 0; t < nc; t++) ncos *= 4;
        for (long long m = 1; m < ncos; m++) {
            v24 x = { 0, 0 }; long long mm = m;
            for (int t = 0; t < nc; t++) { int s = mm & 3; mm >>= 2; if (s) x = vadd(x, vscal(comp[t], s)); }
            if (vwt(x) & 1) continue;
            int ok = 1;
            for (int q = 0; q < nD; q++) if (vwt(vadd(x, Dw[q])) < 8) { ok = 0; break; }
            if (ok) nv++;
        }
        free(Dw);
        printf("%s %d %lld\n", autf, strstr(autf, "x2") ? 0 : 1, nv);
        fflush(stdout);
    }
    return 0;
}
