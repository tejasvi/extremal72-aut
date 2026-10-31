/* pin.c -- pinned single-member LTS test on a real C2 instance (audit, independent code).
   Take a gauge class B0 (random normal-form assignment, or symmetrised over an element of odd order), compute the
   key K(B0^g) for every g in G (key words = constraint words; syndromes as integers, bit t = basis vector t; lex),
   choose a member X = B0^g* (the K-minimal one, or for a negative control a non-minimal one), and write an
   instance in which
     - constraints of level < L allow only X's syndrome (this pins the first L levels to X's prefix),
     - constraints of level >= L keep the REAL bad sets minus X's syndrome,
   so X is a solution and the search is one real subtree.  A sound symmetric search must report X when X is
   K-minimal in its G-orbit (nothing in the lex-leader rule depends on bad sets).
   usage: pin make   PREP INST KEYFILE OUT SEED MODE HIDX L WHICH     (WHICH: min | nonmin)
          pin verify PREP INST KEYFILE SEED MODE HIDX WHICH < engine output   */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
typedef uint64_t u64;
static int N, NG, NC;
static u64 R[18];
static int Ei[171], Ej[171]; static u128 Em[171]; static int Ec[171];
static unsigned char (*PERM)[36];
static u64 *Y; static int *M; static u64 (*UB)[16];
static int NLEV, NCI; static int vstart[64];
static int *Clv, *Cwt, *Cm, *Cnbad; static u128 (*Cfm)[16]; static int (*Cfc)[16]; static int **Cbad;
static u64 rs;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int par(u64 x) { return __builtin_popcountll(x) & 1; }
static int par128(u128 x) { return (__builtin_popcountll((u64)x) + __builtin_popcountll((u64)(x >> 64))) & 1; }
static u128 hex128(const char *s) { u128 v = 0; for (; *s; s++) { int d = (*s <= '9') ? *s - '0' : ((*s | 32) - 'a' + 10); v = (v << 4) | (u128)d; } return v; }
static void read_prep(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    if (fscanf(f, "%d %d %d", &N, &NG, &NC) != 3) exit(2);
    for (int k = 0; k < 18; k++) { unsigned long long x; if (fscanf(f, "%llu", &x) != 1) exit(2); R[k] = x; }
    for (int e = 0; e < 171; e++) { char hx[80]; if (fscanf(f, "%d %d %79s %d", &Ei[e], &Ej[e], hx, &Ec[e]) != 4) exit(2); Em[e] = hex128(hx); }
    PERM = malloc((size_t)NG * 36);
    for (int g = 0; g < NG; g++) for (int i = 0; i < 36; i++) { int p; if (fscanf(f, "%d", &p) != 1) exit(2); PERM[g][i] = (unsigned char)p; }
    Y = malloc(sizeof(u64) * NC); M = malloc(sizeof(int) * NC); UB = malloc(sizeof(u64[16]) * NC);
    for (int c = 0; c < NC; c++) {
        unsigned long long y; if (fscanf(f, "%llu %d", &y, &M[c]) != 2) exit(2); Y[c] = y;
        for (int t = 0; t < M[c]; t++) { unsigned long long u; if (fscanf(f, "%llu", &u) != 1) exit(2); UB[c][t] = u; }
    }
    fclose(f);
}
static void read_inst(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int n; if (fscanf(f, "%d %d %d", &n, &NLEV, &NCI) != 3) exit(4);
    if (n != N || NCI != NC) { fprintf(stderr, "instance/prep mismatch\n"); exit(4); }
    for (int t = 0; t <= NLEV; t++) if (fscanf(f, "%d", &vstart[t]) != 1) exit(4);
    Clv = malloc(sizeof(int) * NC); Cwt = malloc(sizeof(int) * NC); Cm = malloc(sizeof(int) * NC); Cnbad = malloc(sizeof(int) * NC);
    Cfm = malloc(sizeof(u128[16]) * NC); Cfc = malloc(sizeof(int[16]) * NC); Cbad = malloc(sizeof(int *) * NC);
    for (int c = 0; c < NC; c++) {
        if (fscanf(f, "%d %d %d %d", &Clv[c], &Cwt[c], &Cm[c], &Cnbad[c]) != 4) exit(4);
        if (Cm[c] != M[c]) { fprintf(stderr, "m mismatch at %d\n", c); exit(4); }
        for (int t = 0; t < Cm[c]; t++) { char hx[80]; if (fscanf(f, "%79s %d", hx, &Cfc[c][t]) != 2) exit(4); Cfm[c][t] = hex128(hx); }
        Cbad[c] = malloc(sizeof(int) * (Cnbad[c] + 1));
        for (int k = 0; k < Cnbad[c]; k++) if (fscanf(f, "%d", &Cbad[c][k]) != 1) exit(4);
    }
    fclose(f);
}
static void H_of(u128 v, u64 *H) {
    int Gm[18][18];
    for (int e = 0; e < 171; e++) { int b = par128(Em[e] & v) ^ Ec[e]; Gm[Ei[e]][Ej[e]] = b; Gm[Ej[e]][Ei[e]] = b; }
    int ca[36]; for (int a = 0; a < 36; a++) { int c = 0; for (int k = 0; k < 18; k++) if ((R[k] >> a) & 1) c |= 1 << k; ca[a] = c; }
    int Gc[36];
    for (int b = 0; b < 36; b++) { int o = 0; for (int k = 0; k < 18; k++) { int s = 0; for (int l = 0; l < 18; l++) if ((ca[b] >> l) & 1) s ^= Gm[k][l]; if (s) o |= 1 << k; } Gc[b] = o; }
    for (int a = 0; a < 36; a++) { u64 row = 0; for (int b = 0; b < 36; b++) if (__builtin_popcount(ca[a] & Gc[b]) & 1) row |= 1ULL << b; H[a] = row; }
}
static void permH(const u64 *H, const unsigned char *p, u64 *Hg) {
    for (int i = 0; i < 36; i++) { u64 src = H[p[i]], o = 0; for (int j = 0; j < 36; j++) if ((src >> p[j]) & 1) o |= 1ULL << j; Hg[i] = o; }
}
static int syn(const u64 *Hg, int c) {
    u64 r = 0; for (u64 y = Y[c]; y; y &= y - 1) r ^= Hg[__builtin_ctzll(y)];
    int s = 0; for (int t = 0; t < M[c]; t++) if (par(r & UB[c][t])) s |= 1 << t; return s;
}
static int syn_inst(u128 v, int c) { int s = 0; for (int t = 0; t < Cm[c]; t++) if (par128(Cfm[c][t] & v) ^ Cfc[c][t]) s |= 1 << t; return s; }
static u64 H0[36];
static void make_B0(int mode, int hidx) {
    u128 v = 0; for (int i = 0; i < N; i++) if (rnd() & 1) v |= ((u128)1) << i;
    H_of(v, H0);
    for (int c = 0; c < NC; c++) if (syn(H0, c) != syn_inst(v, c)) { fprintf(stderr, "CHAIN CHECK FAILED at constraint %d\n", c); exit(5); }
    if (mode == 1) {
        unsigned char cur[36], tmp[36]; for (int i = 0; i < 36; i++) cur[i] = (unsigned char)i;
        u64 acc[36] = { 0 }, Hk[36]; int ord = 0;
        do {
            permH(H0, cur, Hk); for (int i = 0; i < 36; i++) acc[i] ^= Hk[i]; ord++;
            for (int i = 0; i < 36; i++) tmp[i] = PERM[hidx][cur[i]];
            memcpy(cur, tmp, 36);
            int id = 1; for (int i = 0; i < 36; i++) if (cur[i] != i) id = 0;
            if (id) break;
        } while (ord < 100000);
        if (!(ord & 1)) { fprintf(stderr, "element %d has even order %d\n", hidx, ord); exit(6); }
        memcpy(H0, acc, sizeof acc);
        fprintf(stderr, "B0 symmetrised over an element of order %d\n", ord);
    }
}
static int kc[64], nk = 0;
static void read_key(const char *kf) {
    FILE *f = fopen(kf, "r"); char tok[64]; if (!f || fscanf(f, "%63s", tok) != 1) { fprintf(stderr, "key file\n"); exit(7); }
    unsigned long long wv;
    while (nk < 64 && fscanf(f, "%llu", &wv) == 1) { int c0 = -1; for (int c = 0; c < NC; c++) if (Y[c] == wv) { c0 = c; break; } if (c0 < 0) { fprintf(stderr, "key word without constraint\n"); exit(7); } kc[nk++] = c0; }
    fclose(f);
}
static int cmpkey(const int *a, const int *b) { for (int i = 0; i < nk; i++) { if (a[i] < b[i]) return -1; if (a[i] > b[i]) return 1; } return 0; }
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage\n"); return 1; }
    int make = !strcmp(argv[1], "make");
    read_prep(argv[2]); read_inst(argv[3]); read_key(argv[4]);
    int ai = make ? 6 : 5;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)atoll(argv[ai]) * 0x100000001B3ULL; for (int i = 0; i < 10; i++) rnd();
    int mode = atoi(argv[ai + 1]), hidx = atoi(argv[ai + 2]);
    int L = make ? atoi(argv[ai + 3]) : 0; const char *which = argv[make ? ai + 4 : ai + 3];
    make_B0(mode, hidx);
    /* keys of all members */
    int *K = malloc(sizeof(int) * (size_t)NG * nk); u64 Hg[36];
    for (int g = 0; g < NG; g++) { permH(H0, PERM[g], Hg); for (int i = 0; i < nk; i++) K[(size_t)g * nk + i] = syn(Hg, kc[i]); }
    int gmin = 0; for (int g = 1; g < NG; g++) if (cmpkey(&K[(size_t)g * nk], &K[(size_t)gmin * nk]) < 0) gmin = g;
    int nmin = 0; for (int g = 0; g < NG; g++) if (!cmpkey(&K[(size_t)g * nk], &K[(size_t)gmin * nk])) nmin++;
    int gsel = gmin;
    if (!strcmp(which, "nonmin")) {   /* a member whose key is strictly larger than the minimum */
        int tries = 0; do { gsel = (int)(rnd() % (u64)NG); tries++; } while (!cmpkey(&K[(size_t)gsel * nk], &K[(size_t)gmin * nk]) && tries < 100000);
        if (!cmpkey(&K[(size_t)gsel * nk], &K[(size_t)gmin * nk])) { fprintf(stderr, "all members tie\n"); return 8; }
    }
    int *SX = malloc(sizeof(int) * NC);
    permH(H0, PERM[gsel], Hg); for (int c = 0; c < NC; c++) SX[c] = syn(Hg, c);
    /* members equal to X as classes (same syndromes everywhere) */
    int nsame = 0; for (int g = 0; g < NG; g++) { u64 Hh[36]; permH(H0, PERM[g], Hh); int eq = 1; for (int c = 0; c < NC && eq; c++) if (syn(Hh, c) != SX[c]) eq = 0; nsame += eq; }
    if (make) {
        FILE *o = fopen(argv[5], "w");
        fprintf(o, "%d %d %d\n", N, NLEV, NC);
        for (int t = 0; t <= NLEV; t++) fprintf(o, "%d%c", vstart[t], t == NLEV ? '\n' : ' ');
        for (int c = 0; c < NC; c++) {
            int ns = 1 << M[c]; unsigned char *bad = calloc(ns, 1);
            if (Clv[c] < L) { for (int s = 0; s < ns; s++) bad[s] = 1; }
            else for (int k = 0; k < Cnbad[c]; k++) bad[Cbad[c][k]] = 1;
            bad[SX[c]] = 0;
            int nb = 0; for (int s = 0; s < ns; s++) nb += bad[s];
            fprintf(o, "%d %d %d %d\n", Clv[c], Cwt[c], Cm[c], nb);
            for (int t = 0; t < Cm[c]; t++) { u128 v = Cfm[c][t]; fprintf(o, "%llx%016llx %d\n", (unsigned long long)(v >> 64), (unsigned long long)v, Cfc[c][t]); }
            int first = 1; for (int s = 0; s < ns; s++) if (bad[s]) { fprintf(o, first ? "%d" : " %d", s); first = 0; }
            fprintf(o, "\n"); free(bad);
        }
        fclose(o);
        printf("pinned member g=%d (%s): K-minimal members %d of |G| %d, |Stab(X)| %d, pin levels < %d\n", gsel, which, nmin, NG, nsame, L);
    } else {
        char line[256]; int nsol = 0, isx = 0;
        while (fgets(line, sizeof line, stdin)) {
            if (strncmp(line, "SOLUTION ", 9)) continue;
            char hx[64]; if (sscanf(line + 9, "%63s", hx) != 1) continue;
            u128 v = hex128(hx); nsol++;
            int eq = 1; for (int c = 0; c < NC && eq; c++) if (syn_inst(v, c) != SX[c]) eq = 0;
            isx += eq;
        }
        printf("%s member: solutions %d, equal to X %d -> %s\n", which, nsol, isx,
               !strcmp(which, "min") ? (isx ? "PASS (K-min member kept)" : "FAIL (K-min member lost)") : (isx ? "kept (LTS did not decide)" : "pruned (LTS active)"));
    }
    return 0;
}
