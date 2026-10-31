/* kc: build known Hermitian self-dual [24,12,8] codes over F4 and print their class keys for lookup in cls24.
   Input lines (F4 symbols 0, 1, w = omega, W = omega^2 = conj(omega)):
     G     name row1 ... rowk          explicit generator rows of length 24 (k >= 12)
     M4    name mu rA rB               modified four mu-circulant [I12 | A B ; conj(B)^T conj(A)^T] (Harada 2024, (2))
     DC    name mu rA                  pure double mu-circulant [I12 | A], A 12 x 12 mu-circulant
     BDC   name alpha beta gamma rA    bordered double circulant [I12 | alpha beta..beta ; gamma..gamma^T A], A 11x11
     GOLAY name seed                   extended binary Golay code tensor F4; seed > 0: random monomial image
   Output: name key |Aut_Mon| A8 selfconj d   (key = 192 hex digits as in cls24), or name ERROR reason. */
#include "known.h"
static int sym(char c) { return c == '0' ? 0 : c == '1' ? 1 : c == 'w' ? 2 : c == 'W' ? 3 : -1; }
static int parse_row(const char *s, int n, int *r) {
    if ((int)strlen(s) != n) return -1;
    for (int i = 0; i < n; i++) if ((r[i] = sym(s[i])) < 0) return -1;
    return 0;
}
static int build(char **t, int nt, f4v *gen, int *k, char *err) {
    *k = 12;
    if (!strcmp(t[0], "G")) {
        *k = nt - 2; if (*k < 12 || *k > 60) { strcpy(err, "row count"); return -1; }
        for (int i = 0; i < *k; i++) { int r[24]; if (parse_row(t[2 + i], 24, r)) { strcpy(err, "row"); return -1; } f4v v = { 0, 0 }; for (int j = 0; j < 24; j++) f4set(&v, j, r[j]); gen[i] = v; }
        return 0;
    }
    if (!strcmp(t[0], "M4")) {
        int mu = sym(t[2][0]), ra[6], rb[6]; mat12 A, B, Ac, Bc, M;
        if (nt != 5 || mu < 1 || parse_row(t[3], 6, ra) || parse_row(t[4], 6, rb)) { strcpy(err, "M4 args"); return -1; }
        mucirc(ra, 6, mu, &A); mucirc(rb, 6, mu, &B); conjT(&A, 6, &Ac); conjT(&B, 6, &Bc);
        for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) {
            M.e[i][j] = A.e[i][j]; M.e[i][6 + j] = B.e[i][j]; M.e[6 + i][j] = Bc.e[i][j]; M.e[6 + i][6 + j] = Ac.e[i][j];
        }
        gen_IM(&M, gen); return 0;
    }
    if (!strcmp(t[0], "DC")) {
        int mu = sym(t[2][0]), ra[12]; mat12 A;
        if (nt != 4 || mu < 1 || parse_row(t[3], 12, ra)) { strcpy(err, "DC args"); return -1; }
        mucirc(ra, 12, mu, &A); gen_IM(&A, gen); return 0;
    }
    if (!strcmp(t[0], "BDC")) {
        int al = sym(t[2][0]), be = sym(t[3][0]), ga = sym(t[4][0]), ra[11]; mat12 A, M;
        if (nt != 6 || al < 0 || be < 0 || ga < 0 || parse_row(t[5], 11, ra)) { strcpy(err, "BDC args"); return -1; }
        mucirc(ra, 11, 1, &A);
        M.e[0][0] = al; for (int j = 1; j < 12; j++) { M.e[0][j] = be; M.e[j][0] = ga; }
        for (int i = 0; i < 11; i++) for (int j = 0; j < 11; j++) M.e[1 + i][1 + j] = A.e[i][j];
        gen_IM(&M, gen); return 0;
    }
    if (!strcmp(t[0], "GOLAY")) {
        uint32_t g[12]; golay_gen(g); long seed = nt > 2 ? atol(t[2]) : 0;
        int p[24], s[24]; for (int i = 0; i < 24; i++) { p[i] = i; s[i] = 1; }
        if (seed > 0) {
            rng_t R; rng_seed(&R, (uint64_t)seed);
            for (int i = 23; i > 0; i--) { int j = rng_next(&R) % (i + 1); int x = p[i]; p[i] = p[j]; p[j] = x; }
            for (int i = 0; i < 24; i++) s[i] = 1 + (int)(rng_next(&R) % 3);
        }
        for (int i = 0; i < 12; i++) { f4v v = { 0, 0 }; for (int j = 0; j < 24; j++) if ((g[i] >> j) & 1) f4set(&v, p[j], s[p[j]]); gen[i] = v; }
        return 0;
    }
    if (!strcmp(t[0], "NEI")) {          /* NEI name yhat TYPE args: Nei_H(D, y) = <D cap <y>^perp_H, y>, y = (0^12, yhat) */
        int yh[12]; if (nt < 5 || parse_row(t[2], 12, yh)) { strcpy(err, "NEI args"); return -1; }
        f4v y = { 0, 0 }; for (int j = 0; j < 12; j++) f4set(&y, 12 + j, yh[j]);
        char *t2[80]; int n2 = 0; t2[n2++] = t[3]; t2[n2++] = t[1]; for (int i = 4; i < nt; i++) t2[n2++] = t[i];
        f4v D[64]; int kd;
        if (build(t2, n2, D, &kd, err)) return -1;
        if (f4herm(y, y)) { strcpy(err, "y not isotropic"); return -1; }
        int p = -1; for (int i = 0; i < kd; i++) if (f4herm(D[i], y)) { p = i; break; }
        if (p < 0) { strcpy(err, "y orthogonal to D"); return -1; }
        int hp = f4herm(D[p], y); *k = 0;
        for (int i = 0; i < kd; i++) if (i != p) {
            int hi = f4herm(D[i], y); f4v v = D[i];
            if (hi) v = f4add(v, f4smul(F4MUL[hi][F4INV[hp]], D[p]));
            gen[(*k)++] = v;
        }
        gen[(*k)++] = y; return 0;
    }
    strcpy(err, "unknown type"); return -1;
}
int main(void) {
    static char line[1 << 16];
    while (fgets(line, sizeof line, stdin)) {
        char *t[80]; int nt = 0;
        for (char *p = strtok(line, " \t\r\n"); p && nt < 80; p = strtok(NULL, " \t\r\n")) t[nt++] = p;
        if (nt < 2 || t[0][0] == '#') continue;
        f4v gen[64]; int k; char err[64] = "";
        if (build(t, nt, gen, &k, err)) { printf("%s ERROR %s\n", t[1], err); continue; }
        if (!check_sd(gen, k)) { printf("%s ERROR not_hermitian_self_dual_rank12\n", t[1]); continue; }
        f4v R[64]; memcpy(R, gen, sizeof(f4v) * k); f4rref(R, k, 24, NULL, NULL);
        if (getenv("KCROWS")) { printf("G %s", t[1]); for (int r = 0; r < 12; r++) { putchar(' '); f4print(stdout, R[r], 24); } printf("\n"); }
        long a8; int d = dmin_a8(R, &a8);
        uint64_t A[25]; full_wd(R, 12, 24, A);
        long a8f = (long)A[8]; int df = 0; for (int i = 1; i <= 24; i++) if (A[i]) { df = i; break; }
        if (df != d && !(d == 9 && df > 8)) { printf("%s ERROR dmin_mismatch %d %d\n", t[1], d, df); continue; }
        if (d != 8) { printf("%s ERROR minimum_distance %d\n", t[1], df); continue; }
        if (a8 != a8f) { printf("%s ERROR a8_mismatch %ld %ld\n", t[1], a8, a8f); continue; }
        /* weight distribution must be Table 18 of Araya-Harada with alpha = A8 */
        long al = a8f, W[25] = { 0 };
        W[0] = 1; W[8] = al; W[10] = 18216 - 8 * al; W[12] = 156492 + 28 * al; W[14] = 1147608 - 56 * al; W[16] = 3736557 + 70 * al;
        W[18] = 6248088 - 56 * al; W[20] = 4399164 + 28 * al; W[22] = 1038312 - 8 * al; W[24] = 32778 + al;
        int wok = 1; for (int i = 0; i <= 24; i++) if ((long)A[i] != W[i]) wok = 0;
        f4v key[12], mf[12]; double aut; int sc; char hk[200], hm[200];
        if (keys(R, key, mf, &aut, &sc)) { printf("%s ERROR canon\n", t[1]); continue; }
        hexkey(key, hk); hexkey(mf, hm);
        printf("%s %s %.0f %ld %d %d wd=%s mon=%s\n", t[1], hk, aut, a8f, sc, d, wok ? "ok" : "BAD", hm);
        fflush(stdout);
    }
    return 0;
}
