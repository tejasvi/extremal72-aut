/* unit tests for gf16.h; also dumps MTAB for comparison with the python implementation */
#include "gf16.h"
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #c); exit(1); } } while (0)
static int herm_slow(uint32_t u, uint32_t v) { int s = 0; for (int i = 0; i < 7; i++) s ^= MUL[vget(u,i)][CONJ[vget(v,i)]]; return s; }
static uint64_t rs = 88172645463325252ULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)rs; }
int main(int argc, char **argv) {
    gf_init(); mu5_init();
    /* field axioms */
    for (int a = 0; a < 16; a++) for (int b = 0; b < 16; b++) {
        CHECK(MUL[a][b] == MUL[b][a]);
        for (int c = 0; c < 16; c++) { CHECK(MUL[MUL[a][b]][c] == MUL[a][MUL[b][c]]); CHECK(MUL[a][b ^ c] == (MUL[a][b] ^ MUL[a][c])); }
    }
    for (int a = 1; a < 16; a++) CHECK(MUL[a][INV[a]] == 1);
    { int r = 2, k = 1; while (r != 1) { r = MUL[r][2]; k++; } CHECK(k == 5); }  /* x has order 5 */
    /* conj = y^4 is an automorphism of order 2, fixed field = image of norm (4 elements) */
    int nfix = 0;
    for (int a = 0; a < 16; a++) {
        CHECK(CONJ[CONJ[a]] == a);
        if (CONJ[a] == a) { nfix++; CHECK(a == 0 || a == 1 || a == GF4_W || a == GF4_W2); }
        for (int b = 0; b < 16; b++) { CHECK(CONJ[a ^ b] == (CONJ[a] ^ CONJ[b])); CHECK(CONJ[MUL[a][b]] == MUL[CONJ[a]][CONJ[b]]); CHECK(NRM[MUL[a][b]] == MUL[NRM[a]][NRM[b]]); }
        CHECK(NRM[a] == MUL[a][CONJ[a]]);
        CHECK(NRM[a] == 0 || NRM[a] == 1 || NRM[a] == GF4_W || NRM[a] == GF4_W2);
        CHECK(WTE[SQR[a]] == WTE[a]);
    }
    CHECK(nfix == 4);
    CHECK(MUL[GF4_W][GF4_W] == GF4_W2 && (GF4_W ^ GF4_W2) == 1);
    int n4 = 0, n2 = 0; for (int a = 0; a < 16; a++) { if (WTE[a] == 4) n4++; if (WTE[a] == 2) n2++; }
    CHECK(n4 == 5 && n2 == 10);
    /* Frobenius swaps norm classes 2,3 ; conj fixes classes */
    for (int a = 1; a < 16; a++) { int c = NCLS[a], c2 = NCLS[SQR[a]]; CHECK(c == 1 ? c2 == 1 : c2 == (c ^ 1)); CHECK(NCLS[CONJ[a]] == c); }
    /* packed ops vs slow ops */
    for (int it = 0; it < 1000000; it++) {
        uint32_t u = rnd() & 0x0FFFFFFF, v = rnd() & 0x0FFFFFFF; int c = rnd() & 15;
        CHECK(herm(u, v) == herm_slow(u, v));
        uint32_t w = smul(c, u);
        for (int i = 0; i < 7; i++) CHECK(vget(w, i) == MUL[c][vget(u, i)]);
        CHECK(npat(w) == (c ? pscale(npat(u), NCLS[c]) : 0));
        CHECK(psumnorm(npat(u)) == herm_slow(u, u));
        int g = rnd() % 168;
        CHECK(npat(vperm(u, AUT[g])) == pperm(npat(u), AUT[g]));
        CHECK(Mvec(vperm(u, AUT[g])) == Mvec(u));       /* M invariant under Fano automorphisms */
        CHECK(npat(frob(u)) == pfrob(npat(u)));
        CHECK(Mvec(frob(u)) == Mvec(u));
        CHECK(herm(frob(u), frob(v)) == SQR[herm(u, v)]);
        int z = MU5[rnd() % 5];
        CHECK(Mvec(smul(z, u)) == Mvec(u));
        /* unitary-ness of coordinate scalings by mu5 and of permutations */
        CHECK(herm(vperm(u, AUT[g]), vperm(v, AUT[g])) == herm(u, v));
        if (u) { uint32_t m = minrep(u); int found = 0; for (int k = 0; k < 5; k++) if (smul(MU5[k], u) == m) found = 1; CHECK(found); CHECK(minrep(m) == m); }
    }
    printf("GF4_W=%d GF4_W2=%d MU5=%d %d %d %d %d CLS_REP=%d %d %d\n", GF4_W, GF4_W2, MU5[0], MU5[1], MU5[2], MU5[3], MU5[4], CLS_REP[1], CLS_REP[2], CLS_REP[3]);
    if (argc > 1) { FILE *f = fopen(argv[1], "w"); for (int p = 0; p < 16384; p++) fprintf(f, "%d %d\n", p, MTAB[p]); fclose(f); }
    printf("C unit tests passed\n");
    return 0;
}
