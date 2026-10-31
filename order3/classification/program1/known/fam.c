/* fam: exhaustive enumeration of structured Hermitian self-dual [24,12,8] codes over F4, one line per class.
     fam M mu   modified four mu-circulant codes C_mu(A,B) = [I12 | A B ; conj(B)^T conj(A)^T] (Harada 2024, (2)),
                A, B 6 x 6 mu-circulant, all first rows rA (first nonzero entry 1, or rA = 0) and rB
     fam D mu   pure double mu-circulant codes [I12 | A], A 12 x 12 mu-circulant (mu = 1: double circulant)
     fam B      bordered double circulant codes [I12 | alpha beta..beta ; gamma..gamma^T A], A 11 x 11 circulant,
                all alpha, beta, gamma and first rows
   mu: 1, w (omega) or W (omega^2).  Every candidate is checked in full (Hermitian self-orthogonality of the
   generator rows, rank 12, minimum distance from all words of weight <= 8).
   Output: "C name key aut A8 sc 8 wd=- mon=<monomial canonical form> count=<generator matrices in this class>",
   then "S family ..." with the totals (stdout); the first-row condition is only a prefilter. */
#include "known.h"
#define MAXCL 200000
typedef struct { char key[200], mon[200]; double aut; long a8, cnt; int sc; char ex[64]; } cl_t;
static cl_t *CL; static int ncl;
static long nsd, nd8;
static char (*MF)[200]; static int nmf;           /* distinct monomial canonical forms met */
static void add_mf(const char *m) {
    for (int i = 0; i < nmf; i++) if (!strcmp(MF[i], m)) return;
    if (nmf == MAXCL) { fprintf(stderr, "too many forms\n"); exit(1); }
    strcpy(MF[nmf++], m);
}
static int find_or_add(const char *key) {
    for (int i = 0; i < ncl; i++) if (!strcmp(CL[i].key, key)) return i;   /* few classes: linear scan is fine */
    if (ncl == MAXCL) { fprintf(stderr, "too many classes\n"); exit(1); }
    strcpy(CL[ncl].key, key); CL[ncl].cnt = 0; return ncl++;
}
static void consider(const f4v *gen, const char *ex) {
    if (!check_sd(gen, 12)) return;
    nsd++;
    long a8; if (dmin_a8(gen, &a8) != 8) return;
    nd8++;
    f4v key[12], mf[12]; double aut; int sc; char hk[200], hm[200];
    if (keys(gen, key, mf, &aut, &sc)) { fprintf(stderr, "canon failed\n"); exit(1); }
    hexkey(key, hk); hexkey(mf, hm);
    add_mf(hm);
    int i = find_or_add(hk);
    if (!CL[i].cnt) { strcpy(CL[i].mon, hm); CL[i].aut = aut; CL[i].a8 = a8; CL[i].sc = sc; snprintf(CL[i].ex, sizeof CL[i].ex, "%s", ex); }
    CL[i].cnt++;
}
static void rowstr(const int *r, int n, char *s) { static const char ch[4] = { '0', '1', 'w', 'W' }; for (int i = 0; i < n; i++) s[i] = ch[r[i]]; s[n] = 0; }
static void unrank(long x, int n, int *r) { for (int i = 0; i < n; i++) { r[i] = x & 3; x >>= 2; } }
static int sym(char c) { return c == '1' ? 1 : c == 'w' ? 2 : c == 'W' ? 3 : -1; }
int main(int argc, char **argv) {
    CL = calloc(MAXCL, sizeof(cl_t)); MF = calloc(MAXCL, 200);
    char mode = argv[1][0]; int mu = argc > 2 ? sym(argv[2][0]) : 1;
    char fam[32]; snprintf(fam, sizeof fam, "%c%s", mode, argc > 2 ? argv[2] : "");
    long ncand = 0;
    if (mode == 'M') {
        /* P(r) = first row of A conj(A)^T (A mu-circulant, so the product is mu-circulant): prefilter P(rA) + P(rB) = e0 */
        static int P[4096]; static mat12 Am[4096];
        for (long x = 0; x < 4096; x++) {
            int r[6]; unrank(x, 6, r); mat12 Ac; mucirc(r, 6, mu, &Am[x]); conjT(&Am[x], 6, &Ac);
            int p = 0;
            for (int j = 0; j < 6; j++) { int s = 0; for (int k = 0; k < 6; k++) s ^= gfmul(Am[x].e[0][k], Ac.e[k][j]); p |= s << (2 * j); }
            P[x] = p;
        }
        for (long xa = 0; xa < 4096; xa++) {
            int ra[6]; unrank(xa, 6, ra);
            int fnz = 0; for (int i = 0; i < 6; i++) if (ra[i]) { fnz = ra[i]; break; }
            if (fnz > 1) continue;                     /* C(lA, lB) ~ C(A, B): first nonzero entry of rA is 1 */
            for (long xb = 0; xb < 4096; xb++) {
                if ((P[xa] ^ P[xb]) != 1) continue;
                ncand++;
                mat12 Ac, Bc, M; conjT(&Am[xa], 6, &Ac); conjT(&Am[xb], 6, &Bc);
                for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) {
                    M.e[i][j] = Am[xa].e[i][j]; M.e[i][6 + j] = Am[xb].e[i][j]; M.e[6 + i][j] = Bc.e[i][j]; M.e[6 + i][6 + j] = Ac.e[i][j];
                }
                f4v gen[12]; gen_IM(&M, gen);
                int rb[6]; unrank(xb, 6, rb); char s1[8], s2[8], ex[64]; rowstr(ra, 6, s1); rowstr(rb, 6, s2);
                snprintf(ex, sizeof ex, "rA=%s,rB=%s", s1, s2);
                consider(gen, ex);
            }
        }
    } else if (mode == 'D') {
        for (long x = 0; x < (1L << 24); x++) {
            int r[12]; unrank(x, 12, r);
            f4v v = { 0, 0 }; for (int i = 0; i < 12; i++) f4set(&v, i, r[i]);
            if ((f4wt(v) & 1) == 0) continue;           /* <r, r> = wt(r) mod 2 must be 1 */
            f4v u = v; int ok = 1;
            for (int j = 1; j < 12 && ok; j++) {
                int top = f4get(u, 11); u.a = (u.a << 1) & 0xFFF; u.b = (u.b << 1) & 0xFFF; f4set(&u, 0, gfmul(mu, top));
                if (f4herm(v, u)) ok = 0;
            }
            if (!ok) continue;
            ncand++;
            mat12 A; mucirc(r, 12, mu, &A); f4v gen[12]; gen_IM(&A, gen);
            char s1[16], ex[64]; rowstr(r, 12, s1); snprintf(ex, sizeof ex, "rA=%s", s1);
            consider(gen, ex);
        }
    } else if (mode == 'B') {
        for (long x = 0; x < (1L << 22); x++) {
            int r[11]; unrank(x, 11, r);
            mat12 A; mucirc(r, 11, 1, &A);
            /* prefilter: A conj(A)^T must be I + c J with c in {0, 1} */
            int p[11]; for (int j = 0; j < 11; j++) { int s = 0; for (int k = 0; k < 11; k++) s ^= gfmul(A.e[0][k], gfconj(A.e[j][k])); p[j] = s; }
            int c = p[1], ok = (c <= 1) && (p[0] == (1 ^ c));
            for (int j = 2; j < 11 && ok; j++) if (p[j] != c) ok = 0;
            if (!ok) continue;
            for (int al = 0; al < 4; al++) for (int be = 0; be < 4; be++) for (int ga = 0; ga < 4; ga++) {
                mat12 M; M.e[0][0] = al; for (int j = 1; j < 12; j++) { M.e[0][j] = be; M.e[j][0] = ga; }
                for (int i = 0; i < 11; i++) for (int j = 0; j < 11; j++) M.e[1 + i][1 + j] = A.e[i][j];
                ncand++;
                f4v gen[12]; gen_IM(&M, gen);
                char s1[16], ex[64]; rowstr(r, 11, s1); snprintf(ex, sizeof ex, "a=%d,b=%d,g=%d,rA=%s", al, be, ga, s1);
                consider(gen, ex);
            }
        }
    }
    int nmon = 0; for (int i = 0; i < ncl; i++) nmon += CL[i].sc ? 1 : 2;
    for (int i = 0; i < ncl; i++)
        printf("%s_%d %s %.0f %ld %d 8 wd=- mon=%s count=%ld ex=%s\n", fam, i, CL[i].key, CL[i].aut, CL[i].a8, CL[i].sc, CL[i].mon, CL[i].cnt, CL[i].ex);
    /* number of monomial classes met: distinct monomial canonical forms among the generated codes */
    printf("S %s candidates %ld self-dual %ld d=8 %ld classes(Mon x conj) %d classes(Mon, both conjugates) %d distinct monomial forms met %d\n",
           fam, ncand, nsd, nd8, ncl, nmon, nmf);
    return 0;
}
