/* plant.c -- audit test of the LTS symmetry argument on real C2 instances (independent code).
   Plants the Aut(Y)-orbit of a gauge class B0 into an instance by COMPLEMENT: every constraint's bad set becomes
   "all syndromes except those of the orbit members", so the solution set contains the whole orbit and the search is
   tiny.  The instance stays G-invariant.  A sound symmetric search must report >= 1 orbit member; the plain search
   must report every member.
   usage: plant make   PREP INST OUT SEED MODE [HIDX]
          plant verify PREP INST SEED MODE [HIDX] < solutions (lines 'SOLUTION hex')
   MODE 0: B0 = random normal-form assignment; MODE 1: B0 = sum over <h> of B^{h^k} (h = group element HIDX,
   odd order): an orbit with nontrivial stabiliser (ties in every key component). */
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
/* instance */
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
        if (M[c] > 16) exit(3);
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
/* H (36 rows of 36-bit masks): B(x,z) = x^T H z for x,z in Y, from the Gram matrix of assignment v */
static void H_of(u128 v, u64 *H) {
    int Gm[18][18];
    for (int e = 0; e < 171; e++) { int b = par128(Em[e] & v) ^ Ec[e]; Gm[Ei[e]][Ej[e]] = b; Gm[Ej[e]][Ei[e]] = b; }
    int ca[36]; for (int a = 0; a < 36; a++) { int c = 0; for (int k = 0; k < 18; k++) if ((R[k] >> a) & 1) c |= 1 << k; ca[a] = c; }
    int Gc[36];   /* Gm * c_b as 18-bit vectors */
    for (int b = 0; b < 36; b++) { int o = 0; for (int k = 0; k < 18; k++) { int s = 0; for (int l = 0; l < 18; l++) if ((ca[b] >> l) & 1) s ^= Gm[k][l]; if (s) o |= 1 << k; } Gc[b] = o; }
    for (int a = 0; a < 36; a++) { u64 row = 0; for (int b = 0; b < 36; b++) if (__builtin_popcount(ca[a] & Gc[b]) & 1) row |= 1ULL << b; H[a] = row; }
}
static void permH(const u64 *H, const unsigned char *p, u64 *Hg) {   /* Hg[i][j] = H[p[i]][p[j]] */
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
    /* chain check: identity syndromes from H equal the instance forms at v */
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
        } while (ord < 1000);
        if (!(ord & 1)) { fprintf(stderr, "element %d has even order %d\n", hidx, ord); exit(6); }
        memcpy(H0, acc, sizeof acc);
        fprintf(stderr, "B0 symmetrised over an element of order %d\n", ord);
    }
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    int make = !strcmp(argv[1], "make");
    read_prep(argv[2]); read_inst(argv[3]);
    int ai = make ? 5 : 4;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)atoll(argv[ai]) * 0x100000001B3ULL; for (int i = 0; i < 10; i++) rnd();
    int mode = atoi(argv[ai + 1]); int hidx = (argc > ai + 2) ? atoi(argv[ai + 2]) : 0;
    make_B0(mode, hidx);
    uint16_t *S = malloc(sizeof(uint16_t) * (size_t)NG * NC);
    u64 Hg[36];
    for (int g = 0; g < NG; g++) { permH(H0, PERM[g], Hg); for (int c = 0; c < NC; c++) S[(size_t)g * NC + c] = (uint16_t)syn(Hg, c); }
    /* number of distinct orbit members = distinct syndrome vectors */
    int norb = 0; int *rep = malloc(sizeof(int) * NG);
    for (int g = 0; g < NG; g++) { int dup = 0; for (int q = 0; q < norb && !dup; q++) if (!memcmp(&S[(size_t)g * NC], &S[(size_t)rep[q] * NC], sizeof(uint16_t) * NC)) dup = 1; if (!dup) rep[norb++] = g; }
    if (make) {
        FILE *o = fopen(argv[4], "w");
        fprintf(o, "%d %d %d\n", N, NLEV, NC);
        for (int t = 0; t <= NLEV; t++) fprintf(o, "%d%c", vstart[t], t == NLEV ? '\n' : ' ');
        long tot = 0;
        for (int c = 0; c < NC; c++) {
            int ns = 1 << M[c]; unsigned char *keep = calloc(ns, 1);
            for (int g = 0; g < NG; g++) keep[S[(size_t)g * NC + c]] = 1;
            int nb = 0; for (int s = 0; s < ns; s++) if (!keep[s]) nb++;
            fprintf(o, "%d %d %d %d\n", Clv[c], Cwt[c], Cm[c], nb);
            for (int t = 0; t < Cm[c]; t++) { u128 v = Cfm[c][t]; fprintf(o, "%llx%016llx %d\n", (unsigned long long)(v >> 64), (unsigned long long)v, Cfc[c][t]); }
            int first = 1; for (int s = 0; s < ns; s++) if (!keep[s]) { fprintf(o, first ? "%d" : " %d", s); first = 0; }
            fprintf(o, "\n"); tot += nb; free(keep);
        }
        fclose(o);
        printf("planted |G| %d orbit members %d stabiliser %d; bad entries %ld\n", NG, norb, NG / norb, tot);
    } else {
        char line[256]; int nsol = 0, inorb = 0; int *hit = calloc(norb, sizeof(int));
        while (fgets(line, sizeof line, stdin)) {
            if (strncmp(line, "SOLUTION ", 9)) continue;
            char hx[64]; if (sscanf(line + 9, "%63s", hx) != 1) continue;
            u128 v = hex128(hx); nsol++;
            int found = -1;
            for (int q = 0; q < norb && found < 0; q++) { int ok = 1; for (int c = 0; c < NC && ok; c++) if (syn_inst(v, c) != S[(size_t)rep[q] * NC + c]) ok = 0; if (ok) found = q; }
            if (found >= 0) { inorb++; hit[found]++; }
        }
        int distinct = 0, multi = 0; for (int q = 0; q < norb; q++) { if (hit[q]) distinct++; if (hit[q] > 1) multi++; }
        const char *kf = getenv("KEYFILE");
        if (kf) {   /* K(B) = (s_k0, s_k1, ...) as integers (bit t = syndrome basis vector t), lexicographic */
            FILE *f = fopen(kf, "r"); char tok[64]; int kc[64], nk = 0;
            if (f && fscanf(f, "%63s", tok) == 1) {
                unsigned long long wv;
                while (nk < 64 && fscanf(f, "%llu", &wv) == 1) { int c0 = -1; for (int c = 0; c < NC; c++) if (Y[c] == wv) { c0 = c; break; } if (c0 < 0) { fprintf(stderr, "key word without constraint\n"); exit(7); } kc[nk++] = c0; }
            }
            if (f) fclose(f);
            int best = 0;
            for (int q = 1; q < norb; q++) {
                int cmp = 0;
                for (int i = 0; i < nk && !cmp; i++) { int a = S[(size_t)rep[q] * NC + kc[i]], b = S[(size_t)rep[best] * NC + kc[i]]; cmp = (a < b) ? -1 : (a > b) ? 1 : 0; }
                if (cmp < 0) best = q;
            }
            int nmin = 0, fmin = 0;   /* ties never prune: EVERY K-minimal member must be reported */
            for (int q = 0; q < norb; q++) { int eq = 1; for (int i = 0; i < nk; i++) if (S[(size_t)rep[q] * NC + kc[i]] != S[(size_t)rep[best] * NC + kc[i]]) eq = 0; if (eq) { nmin++; if (hit[q]) fmin++; } }
            printf("key of %d words: K-minimal members %d, reported %d -> %s\n", nk, nmin, fmin, fmin == nmin ? "PASS (all K-min members kept)" : "FAIL (K-min member lost)");
        }
        printf("solutions %d, in the planted orbit %d (distinct members %d of %d, reported twice %d), outside %d\n", nsol, inorb, distinct, norb, multi, nsol - inorb);
    }
    return 0;
}
