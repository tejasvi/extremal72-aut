/* [csp5p_plantdump: build-time variant of prod/frozen_v1/csp5p.c (sha256 d5d9cdf5...) adding env DUMPF] */
/* csp5p: production version of the Golay-labelling CSP (c3explore).  See prod/FORMATS.md.
   Problem: given the forbidden 8-set family F8 and 12-set family F12 on 24 points (derived from a Hermitian
   self-dual [24,12,8] code E: F8 = weight-8 supports, 8-sets meeting one in 7 points, 8-subsets of weight-10
   supports; F12 = weight-12 supports), find/count the labelled Golay codes G' (images pi(G24) of the reference
   Golay code read from BLOCKFILE) none of whose 759 octads lies in F8 and none of whose 2576 dodecads lies in F12.
   Search = csp5 (c3explore, 2026-10-20): M24 normalisation pi(p1..p5) = (c1..c5) [p1..p8 = octad 0 of BLOCKFILE in
   increasing point order, c1<..<c5 = most constrained 5-set of coordinates], A3 rotation (pi(p6) < pi(p7),
   pi(p8)), pi(q1) = smallest free coordinate; forward checking through (size-1)-subset tables; positions 8..15
   (the octad Q of the trio O0, Q, O*) through per-O0 memo tables of the 7 bisection classes.  Every labelled
   Golay code has exactly one normalised pi, so COUNT mode counts labelled Golay codes.
   Usage:  csp5p 24 E CODEFILE BLOCKFILE [first [max]]          (one result line per code)
           csp5p 24 P|Z DENS SEED BLOCKFILE [DENS12]            (gtest4's planted / sextet instance generators)
           csp5p 24 F F8BIN F12BIN BLOCKFILE                    (forbidden families from raw 2^24-bit bitmaps)
           csp5p 16 E CODEFILE G16FILE [first [max]]            (length-48 analogue; G16 = doubly-even [16,8,4])
   Env:    COUNT=1   enumerate all solutions (default: stop at the first)
           PLANT=s   E mode: plant a random labelling per code (seed s + line index), clear its block images
           NOQ=1     generic search for positions 8..15 (no Q phase)                                          */
#include "f4code.h"
#include <time.h>
#include <stdint.h>
#define MAXB 4000
static int n, k;
static int nblk; static u32 blk[MAXB]; static int btype[MAXB], bsize[2];
static u32 *T[2]; static long Tsz[2];
static u32 *R0; static long R0sz;   /* rows for type-0 blocks: index rank(J)*32 + x */
static u32 binom[33][33];
static inline u32 rankset(u32 m) { u32 r = 0; int i = 1; while (m) { int p = __builtin_ctz(m); m &= m - 1; r += binom[p][i++]; } return r; }
static int order[32], posof[32];
static int nfc[32], *fclist[32];
static int fcnext[MAXB]; static u32 pre[MAXB];
static int prept[MAXB][12], npre[MAXB];
static long nodes[33]; static int found; static int pi[32]; static int verbose, mode;
static int countmode = 0; static long nsol; static uint64_t solhash; static u32 srcbasis[16]; static int nsrcb;
static u32 firstsol[16]; static int firstpi[32]; static long nverified, nverify_fail;
static uint64_t hashlist[1 << 16]; static long nhashlist;   /* n=16: distinct labelled codes */
/* hash of a 12-dim binary code given by 12 spanning words: RREF with pivots from bit 23 down, then the FNV
   variant of c3class gcore.h code_hash (same value for the same code) */
static uint64_t code_hash(const u32 *B, int kdim, int nbits) {
    u32 R[16]; memcpy(R, B, sizeof(u32) * kdim); int r = 0;
    for (int c = nbits - 1; c >= 0 && r < kdim; c--) {
        int p = -1; for (int i = r; i < kdim; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        u32 t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < kdim; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < kdim; i++) { h ^= R[i]; h *= 1099511628211ULL; h ^= h >> 29; }
    return h;
}
static void rref_bits(u32 *R, int kdim, int nbits) {
    int r = 0;
    for (int c = nbits - 1; c >= 0 && r < kdim; c--) {
        int p = -1; for (int i = r; i < kdim; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        u32 t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < kdim; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
}
static inline int isforbset(int t, u32 m);
static u32 img(u32 m) { u32 o = 0; while (m) { int p = __builtin_ctz(m); m &= m - 1; o |= 1u << pi[p]; } return o; }
static void record_solution(void) {
    u32 B[16]; for (int i = 0; i < nsrcb; i++) B[i] = img(srcbasis[i]);
    uint64_t h = code_hash(B, nsrcb, n);
    if (mode == 16) {   /* the n=16 search is normalised by one point only: dedupe labelled codes by hash */
        for (long i = 0; i < nhashlist; i++) if (hashlist[i] == h) return;
    }
    if (nhashlist < (1 << 16)) hashlist[nhashlist++] = h;   /* n=24: one normalised pi per labelled code */
    if (nsol == 0) { memcpy(firstsol, B, sizeof(u32) * nsrcb); rref_bits(firstsol, nsrcb, n); memcpy(firstpi, pi, sizeof(int) * n); }
    if (nverified < 100) {   /* independent check of the solution: every block image allowed in the raw bitmaps; pi a bijection */
        int ok = 1; u32 seen = 0; for (int i = 0; i < n; i++) seen |= 1u << pi[i];
        if (seen != (u32)((1ULL << n) - 1)) ok = 0;
        for (int b = 0; b < nblk && ok; b++) if (isforbset(btype[b], img(blk[b]))) ok = 0;
        nverified++; if (!ok) nverify_fail++;
    }
    nsol++; solhash += h;
}
static u32 *forb8bm, *forb12bm;   /* full forbidden bitmaps (for planted test and the prefix) */
static inline int isforbset(int t, u32 m) { u32 *bm = t ? forb12bm : forb8bm; return (bm[m >> 5] >> (m & 31)) & 1; }
static inline void setbm(u32 *bm, u32 m) { bm[m >> 5] |= 1u << (m & 31); }
static inline void clrbm(u32 *bm, u32 m) { bm[m >> 5] &= ~(1u << (m & 31)); }
static int fcpre[MAXB][12], nfcpre[MAXB];   /* points of pre[b] other than the second-to-last point */
/* ---- phase-2 (Q) data: planes of the trio structure ---- */
static int qphase = 1;                 /* use the specialised Q phase for positions 8..15 (mode 24) */
static int nplane; static u32 pl_src[16]; static int pl_k[16], pl_sp[16], pl_last[16];
static u32 tk_src[7][2];               /* tetrads T_k, T'_k of O0 (source) */
static u32 timg[7][2];                 /* their images */
static int qblk;                       /* block index of Q */
static unsigned char memo[7][65536];
static u32 rowmemo[7][560]; static u32 gen = 0;   /* (gen<<16) | allowed local-y mask for (class, local 3-mask) */
static int glob[16];
static int loc[32];
static inline int planeok(int k, u32 lm, u32 em) {   /* lm = local 4-mask, em = E-coordinate 4-mask */
    unsigned char v = memo[k][lm];
    if (v) return v == 1;
    int ok = !isforbset(0, timg[k][0] | em) && !isforbset(0, timg[k][1] | em);
    memo[k][lm] = ok ? 1 : 2; return ok;
}
static void search(int pos, u32 used, u32 *dom);
/* plane membership per source point and per position */
static int npl_of_pt[32], pl_of_pt[32][8];
static int nfcpl[32], fcpl[32][8];          /* planes whose second-to-last point is at this position */
static u32 qmemo[11440];                    /* (gen<<16) | allowed local y for Q's last point given local 7-mask */
static int qpts_local_pos[8]; static int getenv_stop16;
static void qsearch_l(int pos, u32 usedl, u32 *doml, u32 *part, u32 qmask_l) {
    nodes[pos]++;
    int p = order[pos];
    u32 cand = doml[pos] & ~usedl & 0xffff;
    if (pos == 8) cand &= cand & (-cand);          /* q1 -> smallest remaining coordinate (local 0) */
    u32 nd[24], np_[16];
    while (cand) {
        int x = __builtin_ctz(cand); cand &= cand - 1;
        u32 nu = usedl | (1u << x);
        for (int t = pos + 1; t < 16; t++) nd[t] = doml[t];
        int ok = 1;
        for (int j = 0; j < nfcpl[pos]; j++) {
            int i = fcpl[pos][j]; int k = pl_k[i]; u32 l3 = part[i] | (1u << x);
            u32 r3 = rankset(l3); u32 rm = rowmemo[k][r3];
            if ((rm >> 16) != gen) {
                u32 e3 = 0; u32 m = l3; while (m) { int ly = __builtin_ctz(m); m &= m - 1; e3 |= 1u << glob[ly]; }
                u32 al = 0;
                for (int ly = 0; ly < 16; ly++) { if ((l3 >> ly) & 1) continue; int y = glob[ly];
                    if (!isforbset(0, timg[k][0] | e3 | (1u << y)) && !isforbset(0, timg[k][1] | e3 | (1u << y))) al |= 1u << ly; }
                rm = (gen << 16) | al; rowmemo[k][r3] = rm;
            }
            int t = pl_last[i]; nd[t] &= rm & 0xffff;
            if (!(nd[t] & ~nu)) { ok = 0; break; }
        }
        if (!ok) continue;
        u32 nq = qmask_l | (1u << x);
        if (pos == 14) {
            u32 r7 = rankset(nq); u32 qm = qmemo[r7];
            if ((qm >> 16) != gen) {
                u32 e7 = 0; u32 m = nq; while (m) { int ly = __builtin_ctz(m); m &= m - 1; e7 |= 1u << glob[ly]; }
                u32 al = 0; for (int ly = 0; ly < 16; ly++) { if ((nq >> ly) & 1) continue; if (!isforbset(0, e7 | (1u << glob[ly]))) al |= 1u << ly; }
                qm = (gen << 16) | al; qmemo[r7] = qm;
            }
            nd[15] &= qm & 0xffff; if (!(nd[15] & ~nu)) continue;
        }
        for (int i = 0; i < nplane; i++) np_[i] = part[i];
        for (int j = 0; j < npl_of_pt[p]; j++) np_[pl_of_pt[p][j]] |= 1u << x;
        pi[p] = glob[x];
        if (pos == 15) {
            /* placement complete: phase 3 with global domains (all remaining coordinates) */
            u32 usedg = 0; for (int i = 0; i < 16; i++) usedg |= 1u << pi[order[i]];
            u32 dg[32]; for (int i = 0; i < n; i++) dg[i] = (1u << n) - 1;
            if (getenv_stop16) nodes[16]++; else search(16, usedg, dg);
        } else qsearch_l(pos + 1, nu, nd, np_, nq);
        if (found && !countmode) return;
    }
}
static void search(int pos, u32 used, u32 *dom) {
    nodes[pos]++;
    if (pos == n) { found = 1; record_solution(); return; }
    int p = order[pos];
    u32 cand = dom[pos] & ~used;
    if (mode == 24 && pos >= 6 && pos <= 7) cand &= ~((2u << pi[order[5]]) - 1);
    if (mode == 24 && pos == 8) { u32 rem = ((1u << n) - 1) & ~used; cand &= rem & (-rem); }
    if (!cand) return;
    int nf = nfc[pos]; const u32 *rows[MAXB]; u32 jm[MAXB]; unsigned char have[MAXB];
    memset(have, 0, nf);
    u32 ndom[32];
    while (cand) {
        int x = __builtin_ctz(cand); cand &= cand - 1;
        pi[p] = x; u32 nu = used | (1u << x);
        memcpy(ndom, dom, sizeof(u32) * n);
        int ok = 1;
        for (int i = 0; i < nf; i++) {
            int b = fclist[pos][i]; int t = fcnext[b];
            if (!have[i]) { u32 im = 0; for (int j = 0; j < nfcpre[b]; j++) im |= 1u << pi[fcpre[b][j]]; jm[i] = im; if (btype[b] == 0) rows[i] = R0 + (long)rankset(im) * 32; have[i] = 1; }
            u32 bad = btype[b] == 0 ? rows[i][x] : T[1][rankset(jm[i] | (1u << x))];
            ndom[t] &= ~bad;
            if (!(ndom[t] & ~nu)) { ok = 0; break; }
        }
        if (!ok) continue;
        if (mode == 24 && qphase && pos == 7) {
            /* O0 labelled: set up the Q phase */
            for (int k = 0; k < 7; k++) for (int h = 0; h < 2; h++) { u32 e = 0, m = tk_src[k][h]; while (m) { int q = __builtin_ctz(m); m &= m - 1; e |= 1u << pi[q]; } timg[k][h] = e; }
            u32 rem = ((1u << n) - 1) & ~nu; int l = 0; for (int c = 0; c < n; c++) if ((rem >> c) & 1) loc[c] = l++;
            gen = (gen + 1) & 0xffff; if (!gen) { memset(rowmemo, 0, sizeof rowmemo); memset(qmemo, 0, sizeof qmemo); gen = 1; }
            for (int c = 0; c < n; c++) if ((rem >> c) & 1) glob[loc[c]] = c;
            { u32 dl[24]; for (int t = 0; t < 24; t++) dl[t] = 0xffff; u32 part[16]; for (int i = 0; i < 16; i++) part[i] = 0;
              qsearch_l(8, 0, dl, part, 0); }
        } else search(pos + 1, nu, ndom);
        if (found && !countmode) return;
    }
}
static void addT(int t, u32 F) {      /* register forbidden image F of type t */
    for (u32 a = F; a; a &= a - 1) { u32 y = a & -a; T[t][rankset(F & ~y)] |= y; }
    if (t == 0) for (u32 a = F; a; a &= a - 1) { u32 x = a & -a; int xi = __builtin_ctz(x);
        for (u32 b = F & ~x; b; b &= b - 1) { u32 y = b & -b; R0[(long)rankset(F & ~x & ~y) * 32 + xi] |= y; } }
}
/* ---- gtest4-compatible instance generators (c3class gcore.h / gtest4.c P and Z modes, replicated) ---- */
typedef struct { uint64_t s[4]; } xrng;
static inline uint64_t xrotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t xnext(xrng *r) {
    uint64_t *s = r->s, res = xrotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = xrotl(s[3], 45);
    return res;
}
static inline void xseed(xrng *r, uint64_t seed) {
    for (int i = 0; i < 4; i++) {
        uint64_t z = (seed += 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        r->s[i] = z ^ (z >> 31);
    }
}
static void qr_golay_gen(u32 *gen) {        /* cyclic [23,12,7] QR code g(x) = 1+x^2+x^4+x^5+x^6+x^10+x^11, parity at bit 23 */
    u32 g = (1u << 0) | (1u << 2) | (1u << 4) | (1u << 5) | (1u << 6) | (1u << 10) | (1u << 11);
    for (int s2 = 0; s2 < 12; s2++) { u32 r = g << s2; if (__builtin_popcount(r) & 1) r |= 1u << 23; gen[s2] = r; }
}
static u32 applyperm(const int *p, u32 w) { u32 o = 0; for (; w; w &= w - 1) o |= 1u << p[__builtin_ctz(w)]; return o; }
static double wallnow(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int hexval(int c) { if (c >= '0' && c <= '9') return c - '0'; if (c >= 'a' && c <= 'f') return c - 'a' + 10; if (c >= 'A' && c <= 'F') return c - 'A' + 10; return -1; }
/* parse one code line into k rows; returns 1 on success; sets idbuf (from "id=..." token) if present */
static int parse_code(const char *line, int kk, vec *g, char *idbuf) {
    idbuf[0] = 0;
    const char *q = line; while (*q == ' ' || *q == '\t') q++;
    int tl = 0; while (q[tl] && q[tl] != ' ' && q[tl] != '\t' && q[tl] != '\n' && q[tl] != '\r') tl++;
    const char *rest;
    if (tl >= 16 * kk) {              /* format B (c3class/gtest4): rows as 8 hex (a = lo plane) + 8 hex (b = hi plane) */
        for (int r = 0; r < kk; r++) {
            u32 a = 0, b = 0;
            for (int c = 0; c < 8; c++) { int v = hexval(q[16 * r + c]); if (v < 0) return 0; a = a * 16 + v; }
            for (int c = 0; c < 8; c++) { int v = hexval(q[16 * r + 8 + c]); if (v < 0) return 0; b = b * 16 + v; }
            g[r].lo = a; g[r].hi = b;
        }
        rest = q + tl;
    } else {                           /* format A (c3explore): 2k hex tokens "lo hi" per row, optional "| comment" */
        char *e; const char *c = q;
        for (int r = 0; r < kk; r++) {
            g[r].lo = strtoul(c, &e, 16); if (e == c) return 0; c = e;
            g[r].hi = strtoul(c, &e, 16); if (e == c) return 0; c = e;
        }
        rest = c;
    }
    const char *idp = strstr(rest, "id=");
    if (idp) { int j = 0; idp += 3; while (*idp && *idp != ' ' && *idp != '\t' && *idp != '\n' && *idp != '\r' && j < 63) idbuf[j++] = *idp++; idbuf[j] = 0; }
    return 1;
}
/* self-orthogonality check of the generator rows and rank = k */
static int check_code(vec *g, int kk) {
    for (int a = 0; a < kk; a++) for (int b = 0; b < kk; b++) if (vherm(g[a], g[b])) return 0;
    vec t[16]; memcpy(t, g, sizeof(vec) * kk); int pv[16];
    return vrref(t, kk, n, pv) == kk;
}
static void build_tables(long *nf) {
    memset(T[0], 0, sizeof(u32) * Tsz[0]); memset(T[1], 0, sizeof(u32) * Tsz[1]); memset(R0, 0, sizeof(u32) * R0sz);
    nf[0] = nf[1] = 0;
    for (int t = 0; t < 2; t++) { u32 *bm = t ? forb12bm : forb8bm; long words = (1L << n) / 32;
        for (long wi = 0; wi < words; wi++) { u32 x = bm[wi]; while (x) { int bpos = __builtin_ctz(x); x &= x - 1; u32 F = (u32)(wi * 32 + bpos); if (__builtin_popcount(F) == bsize[t]) { addT(t, F); nf[t]++; } } } }
}
static uint64_t solhashes_store[1 << 16]; static long nstore;
static void run_instance(void) {
    u32 dom[32]; for (int i = 0; i < n; i++) dom[i] = (1u << n) - 1;
    memset(nodes, 0, sizeof nodes); found = 0; nsol = 0; solhash = 0; nhashlist = 0; nverified = 0; nverify_fail = 0;
    if (mode == 24) {
        int bestc[5] = {0,1,2,3,4}; long bestf = -1;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) for (int c = b + 1; c < n; c++) for (int d = c + 1; d < n; d++) for (int e = d + 1; e < n; e++) {
            u32 P = (1u << a) | (1u << b) | (1u << c) | (1u << d) | (1u << e); long f = 0;
            u32 rest = ((1u << n) - 1) & ~P;
            for (u32 x = rest; x; x &= x - 1) { u32 x1 = x & -x; for (u32 y = x & (x - 1); y; y &= y - 1) f += __builtin_popcount(T[0][rankset(P | x1 | (y & -y))] & ~(P | x1 | (y & -y)) & ~((y & -y) - 1)); }
            if (f > bestf) { bestf = f; bestc[0] = a; bestc[1] = b; bestc[2] = c; bestc[3] = d; bestc[4] = e; }
        }
        u32 used = 0; for (int i = 0; i < 5; i++) { pi[order[i]] = bestc[i]; used |= 1u << bestc[i]; }
        for (int pos = 0; pos < 5; pos++) for (int i = 0; i < nfc[pos]; i++) {
            int b = fclist[pos][i]; u32 im = 0; for (int j = 0; j < npre[b]; j++) im |= 1u << pi[prept[b][j]];
            dom[fcnext[b]] &= ~T[btype[b]][rankset(im)];
        }
        search(5, used, dom);
    } else { pi[order[0]] = 0; search(1, 1, dom); }
}
static void print_result(const char *id, double wall, double cpu, double prep, long n8, long n10, long n12, const long *nf, const char *extra) {
    long tot = 0; for (int i = 0; i <= n; i++) tot += nodes[i];
    printf("id=%s res=%s nsol=%ld%s hash=%016llx nodes=%ld wall=%.3f cpu=%.3f prep=%.3f pw8=%ld pw10=%ld pw12=%ld f8=%ld f12=%ld",
           id, found ? "SAT" : "UNSAT", nsol, (found && !countmode) ? "+" : "", (unsigned long long)solhash, tot, wall, cpu, prep, n8, n10, n12, nf[0], nf[1]);
    if (found) {
        printf(" verified=%ld/%ld", nverified - nverify_fail, nverified);
        printf(" golay="); for (int i = 0; i < nsrcb; i++) printf("%s%06x", i ? "," : "", firstsol[i]);
        printf(" pi="); for (int i = 0; i < n; i++) printf("%s%d", i ? "," : "", firstpi[i]);
    }
    if (extra && *extra) printf(" %s", extra);
    printf("\n"); fflush(stdout);
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: csp5p 24|16 E CODEFILE BLOCKFILE [first [max]]  |  csp5p 24 P|Z DENS SEED BLOCKFILE [DENS12]\n"); return 1; }
    mode = atoi(argv[1]); n = mode; k = n / 2; char kind = argv[2][0];
    if ((n != 24 && n != 16) || (kind != 'E' && kind != 'P' && kind != 'Z' && kind != 'F') || (n == 16 && kind != 'E')) { fprintf(stderr, "bad mode\n"); return 1; }
    const char *bfile = argv[4];
    if (kind == 'P' || kind == 'Z' || kind == 'F') { if (argc < 6) { fprintf(stderr, "P/Z need DENS SEED BLOCKFILE; F needs F8BIN F12BIN BLOCKFILE\n"); return 1; } bfile = argv[5]; }
    countmode = getenv("COUNT") ? atoi(getenv("COUNT")) : 0; verbose = getenv("VERBOSE") ? 1 : 0;
    for (int a = 0; a <= 32; a++) { binom[a][0] = 1; for (int b = 1; b <= 32; b++) binom[a][b] = a ? binom[a - 1][b - 1] + binom[a - 1][b] : 0; }
    FILE *fb = fopen(bfile, "r"); if (!fb) { fprintf(stderr, "cannot open block file %s\n", bfile); return 2; }
    if (mode == 24) {
        for (int i = 0; i < 759 + 2576; i++) { if (fscanf(fb, "%u", &blk[i]) != 1) return 2; btype[i] = i < 759 ? 0 : 1; }
        nblk = 759 + 2576; bsize[0] = 8; bsize[1] = 12;
    } else {
        u32 w; nblk = 0;
        while (fscanf(fb, "%u", &w) == 1) { int c = __builtin_popcount(w); if (c == 4) { blk[nblk] = w; btype[nblk++] = 0; } else if (c == 8) { blk[nblk] = w; btype[nblk++] = 1; } }
        bsize[0] = 4; bsize[1] = 8;
    }
    fclose(fb);
    for (int t = 0; t < 2; t++) { Tsz[t] = binom[n][bsize[t] - 1]; T[t] = malloc(sizeof(u32) * Tsz[t]); }
    forb8bm = malloc(1u << (n - 3)); forb12bm = malloc(1u << (n - 3));
    R0sz = (long)binom[n][bsize[0] - 2] * 32; R0 = malloc(sizeof(u32) * R0sz);
    /* greedy point order */
    u32 chosen = 0; int np = 0;
    if (mode == 24) { u32 o0 = blk[0]; while (o0) { int p = __builtin_ctz(o0); o0 &= o0 - 1; order[np++] = p; chosen |= 1u << p; } }
    else { order[np++] = 0; chosen = 1; }
    while (np < n) {
        int best = -1; long bs = -1;
        for (int p = 0; p < n; p++) if (!((chosen >> p) & 1)) {
            u32 c2 = chosen | (1u << p); long s = 0;
            for (int b = 0; b < nblk; b++) { int t = btype[b]; u32 m = blk[b]; if ((m & c2) == m && (m >> p) & 1) s += 1000000; else if (__builtin_popcount(m & ~c2) == 1 && (m >> p) & 1) s += (t == 0 ? 1000 : 1); }
            if (s > bs) { bs = s; best = p; }
        }
        order[np++] = best; chosen |= 1u << best;
    }
    for (int i = 0; i < n; i++) posof[order[i]] = i;
    for (int i = 0; i < n; i++) fclist[i] = malloc(sizeof(int) * MAXB);
    for (int b = 0; b < nblk; b++) {
        int lp = -1, sp = -1; u32 m = blk[b];
        while (m) { int p = __builtin_ctz(m); m &= m - 1; int q = posof[p]; if (q > lp) { sp = lp; lp = q; } else if (q > sp) sp = q; }
        fcnext[b] = lp; pre[b] = blk[b] & ~(1u << order[lp]);
        npre[b] = 0; for (u32 mm = pre[b]; mm; mm &= mm - 1) prept[b][npre[b]++] = __builtin_ctz(mm);
        fclist[sp][nfc[sp]++] = b;
    }
    for (int pos = 0; pos < n; pos++) {
        int cnt[32] = {0}; for (int i = 0; i < nfc[pos]; i++) cnt[fcnext[fclist[pos][i]]]++;
        /* simple insertion sort: key = (type, -cnt[target], target) */
        for (int i = 1; i < nfc[pos]; i++) { int b = fclist[pos][i], j = i - 1;
            #define KEY(bb) (btype[bb] * 100000 + (1000 - cnt[fcnext[bb]]) * 32 + fcnext[bb])
            while (j >= 0 && KEY(fclist[pos][j]) > KEY(b)) { fclist[pos][j + 1] = fclist[pos][j]; j--; }
            fclist[pos][j + 1] = b; }
        for (int i = 0; i < nfc[pos]; i++) { int b = fclist[pos][i]; nfcpre[b] = 0;
            for (int j = 0; j < npre[b]; j++) if (prept[b][j] != order[pos]) fcpre[b][nfcpre[b]++] = prept[b][j]; }
    }
    if (mode == 24) {
        u32 O0 = 0, Qm = 0; for (int i = 0; i < 8; i++) O0 |= 1u << order[i]; for (int i = 8; i < 16; i++) Qm |= 1u << order[i];
        qblk = -1; for (int b = 0; b < 759; b++) if (blk[b] == Qm) qblk = b;
        if (qblk < 0) { fprintf(stderr, "positions 8..15 do not form an octad; Q phase off\n"); qphase = 0; }
        int nk = 0; nplane = 0;
        for (int b = 0; b < 759 && qphase; b++) {
            u32 o = blk[b]; if (__builtin_popcount(o & O0) != 4 || __builtin_popcount(o & Qm) != 4) continue;
            u32 U = o & Qm, Tt = o & O0; int k = -1;
            for (int kk = 0; kk < nk; kk++) if (tk_src[kk][0] == Tt || tk_src[kk][1] == Tt) k = kk;
            if (k < 0) { k = nk++; tk_src[k][0] = Tt; tk_src[k][1] = O0 ^ Tt; }
            int seen = -1; for (int i = 0; i < nplane; i++) if (pl_src[i] == U) seen = i;
            if (seen >= 0) continue;
            pl_src[nplane] = U; pl_k[nplane] = k;
            int lp = -1, sp = -1; u32 m = U; while (m) { int q = __builtin_ctz(m); m &= m - 1; int ps = posof[q]; if (ps > lp) { sp = lp; lp = ps; } else if (ps > sp) sp = ps; }
            pl_last[nplane] = lp; pl_sp[nplane] = sp; nplane++;
        }
        if (qphase && (nk != 7 || nplane != 14)) { fprintf(stderr, "unexpected trio structure %d %d\n", nk, nplane); return 3; }
        if (getenv("NOQ")) qphase = 0;
        for (int i = 0; i < nplane; i++) { u32 m = pl_src[i]; while (m) { int q = __builtin_ctz(m); m &= m - 1; pl_of_pt[q][npl_of_pt[q]++] = i; }
            fcpl[pl_sp[i]][nfcpl[pl_sp[i]]++] = i; }
        getenv_stop16 = getenv("STOP16") != NULL;
    }
    if (verbose) { fprintf(stderr, "order:"); for (int i = 0; i < n; i++) fprintf(stderr, " %d(fc%d)", order[i], nfc[i]); fprintf(stderr, "\n"); }
    /* reference code basis (for hashing labelled codes) */
    { u32 tmp[MAXB]; int nt = 0; for (int b = 0; b < nblk; b++) tmp[nt++] = blk[b];
      nsrcb = 0; for (int i = 0; i < nt; i++) { u32 v = tmp[i]; for (int j = 0; j < nsrcb; j++) { int hb = 31 - __builtin_clz(srcbasis[j]); if ((v >> hb) & 1) v ^= srcbasis[j]; }
          if (v) { srcbasis[nsrcb++] = v; /* keep echelon by highest bit */
              for (int a = nsrcb - 1; a > 0 && (31 - __builtin_clz(srcbasis[a])) > (31 - __builtin_clz(srcbasis[a - 1])); a--) { u32 t = srcbasis[a]; srcbasis[a] = srcbasis[a - 1]; srcbasis[a - 1] = t; } } }
      /* the echelon above is only partially reduced; make it a proper basis by full elimination */
      u32 Bt[16]; memcpy(Bt, srcbasis, sizeof(u32) * nsrcb); rref_bits(Bt, nsrcb, n); memcpy(srcbasis, Bt, sizeof(u32) * nsrcb);
      if (nsrcb != k) { fprintf(stderr, "reference code dimension %d != %d\n", nsrcb, k); return 2; } }
    int h1 = k / 2, h2 = k - h1;
    vec *A = malloc(sizeof(vec) << (2 * h1)), *B = malloc(sizeof(vec) << (2 * h2));
    u32 *sA = malloc(sizeof(u32) * 400000), *sB = malloc(sizeof(u32) * 400000), *sC = malloc(sizeof(u32) * 800000);
    if (kind == 'F') {     /* forbidden families from raw 2^24-bit bitmaps (bit m in byte m>>3, position m&7) */
        double t0 = wallnow(); clock_t c0 = clock();
        /* two accepted layouts per file: raw (2^21 bytes, bit m = mask m) or compact (ceil(C(24,s)/8) bytes, bit r =
           colex rank r among s-subsets, as in c3class gcore.h); detected from the file size */
        long fsz[2]; unsigned char *bb[2]; int sz[2] = {8, 12};
        for (int t = 0; t < 2; t++) {
            FILE *f = fopen(argv[3 + t], "rb"); if (!f) { fprintf(stderr, "cannot open %s\n", argv[3 + t]); return 2; }
            fseek(f, 0, SEEK_END); fsz[t] = ftell(f); fseek(f, 0, SEEK_SET);
            long craw = 1L << 21, ccomp = ((long)binom[24][sz[t]] + 7) / 8;
            if (fsz[t] != craw && fsz[t] != ccomp) { fprintf(stderr, "%s: size %ld is neither raw (%ld) nor compact (%ld)\n", argv[3 + t], fsz[t], craw, ccomp); return 2; }
            bb[t] = malloc(fsz[t]); if (fread(bb[t], 1, fsz[t], f) != (size_t)fsz[t]) { fprintf(stderr, "short read %s\n", argv[3 + t]); return 2; } fclose(f);
        }
        memset(forb8bm, 0, 1u << (n - 3)); memset(forb12bm, 0, 1u << (n - 3));
        long bad = 0;
        for (u32 m = 0; m < (1u << 24); m++) {
            int c = __builtin_popcount(m);
            for (int t = 0; t < 2; t++) {
                int isset;
                if (fsz[t] == (1L << 21)) { isset = (bb[t][m >> 3] >> (m & 7)) & 1; if (isset && c != sz[t]) { bad++; continue; } if (c != sz[t]) continue; }
                else { if (c != sz[t]) continue; u32 r = rankset(m); isset = (bb[t][r >> 3] >> (r & 7)) & 1; }
                if (isset) setbm(t ? forb12bm : forb8bm, m);
            }
        }
        if (bad) fprintf(stderr, "warning: %ld raw bitmap entries of the wrong size ignored\n", bad);
        fprintf(stderr, "F mode layouts: forb8 %s, forb12 %s\n", fsz[0] == (1L << 21) ? "raw" : "compact", fsz[1] == (1L << 21) ? "raw" : "compact");
        long nf[2]; build_tables(nf);
        double prep = wallnow() - t0;
        run_instance();
        char id[600]; snprintf(id, sizeof id, "F:%s", argv[3]);
        print_result(id, wallnow() - t0, (double)(clock() - c0) / CLOCKS_PER_SEC, prep, 0, 0, 0, nf, "");
        return 0;
    }
    if (kind == 'P' || kind == 'Z') {
        double dens = atof(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10); double dens12 = argc > 6 ? atof(argv[6]) : 0;
        double t0 = wallnow(); clock_t c0 = clock();
        xrng R; xseed(&R, seed);
        unsigned char *keep = calloc(1 << 21, 1);
        u32 gen[12]; qr_golay_gen(gen); u32 W[4096];
        for (int m = 0; m < 4096; m++) { u32 w = 0; for (int i = 0; i < 12; i++) if ((m >> i) & 1) w ^= gen[i]; W[m] = w; }
        int pp[24]; for (int i = 0; i < 24; i++) pp[i] = i;
        u32 sext[6]; for (int i = 0; i < 6; i++) sext[i] = 0xFu << (4 * i);
        if (kind == 'P') {
            for (int i = 23; i > 0; i--) { int j = (int)(xnext(&R) % (uint64_t)(i + 1)); int t = pp[i]; pp[i] = pp[j]; pp[j] = t; }
            for (int m = 0; m < 4096; m++) { u32 w = applyperm(pp, W[m]); keep[w >> 3] |= 1 << (w & 7); }
        } else {
            for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) { u32 w = sext[i] | sext[j]; keep[w >> 3] |= 1 << (w & 7); }
        }
        memset(forb8bm, 0, 1u << (n - 3)); memset(forb12bm, 0, 1u << (n - 3));
        for (u32 s2 = 0; s2 < (1u << 24); s2++) {
            int c = __builtin_popcount(s2); int kp = (keep[s2 >> 3] >> (s2 & 7)) & 1;
            if (c == 8 && !kp) {
                int bad = 0;
                if (kind == 'Z') { int par = __builtin_popcount(s2 & sext[0]) & 1; for (int i = 1; i < 6; i++) if ((__builtin_popcount(s2 & sext[i]) & 1) != par) bad = 1; }
                if (bad || (xnext(&R) >> 11) * 0x1.0p-53 < dens) setbm(forb8bm, s2);
            }
            if (c == 12 && !kp && dens12 > 0 && (xnext(&R) >> 11) * 0x1.0p-53 < dens12) setbm(forb12bm, s2);
        }
        long nf[2]; build_tables(nf);
        double prep = wallnow() - t0;
        run_instance();
        char extra[256] = "";
        if (kind == 'P') {
            u32 Bp[12]; for (int i = 0; i < 12; i++) Bp[i] = applyperm(pp, gen[i]);
            uint64_t hp = code_hash(Bp, 12, 24);
            int pf = 0; for (long i = 0; i < nhashlist; i++) if (hashlist[i] == hp) pf = 1;
            snprintf(extra, sizeof extra, "planted_hash=%016llx planted_found=%d", (unsigned long long)hp, pf);
        }
        char id[96]; snprintf(id, sizeof id, "%s:dens=%g:seed=%llu:dens12=%g", kind == 'P' ? "planted" : "sextetZ", dens, (unsigned long long)seed, dens12);
        print_result(id, wallnow() - t0, (double)(clock() - c0) / CLOCKS_PER_SEC, prep, 0, 0, 0, nf, extra);
        return 0;
    }
    /* E mode */
    long first = argc > 5 ? atol(argv[5]) : 0, maxc = argc > 6 ? atol(argv[6]) : (1L << 40);
    FILE *fc = fopen(argv[3], "r"); if (!fc) { fprintf(stderr, "cannot open code file %s\n", argv[3]); return 2; }
    char line[16384]; long li = -1;
    while (fgets(line, sizeof line, fc)) {
        li++;
        if (li < first) continue;
        if (li >= first + maxc) break;
        vec g[16]; char idb[64]; char id[96];
        int okp = parse_code(line, k, g, idb);
        if (idb[0]) snprintf(id, sizeof id, "%s", idb); else snprintf(id, sizeof id, "%ld", li);
        if (!okp) { char *e = line; while (*e == ' ' || *e == '\t') e++; if (*e == '\n' || *e == '#' || *e == 0) continue; printf("id=%s res=ERROR parse\n", id); fflush(stdout); continue; }
        if (!check_code(g, k)) { printf("id=%s res=ERROR not_hermitian_self_orthogonal_or_rank\n", id); fflush(stdout); continue; }
        double t0 = wallnow(); clock_t c0 = clock();
        combos(g, h1, A); combos(g + h1, h2, B);
        long nA = 1L << (2 * h1), nB = 1L << (2 * h2);
        int wa = mode == 24 ? 8 : 6, wb = mode == 24 ? 10 : 8;
        long na = 0, nb = 0, nc = 0; int dmin = 99;
        for (long i = 0; i < nA; i++) for (long j = 0; j < nB; j++) {
            if (!i && !j) continue;
            u32 s2 = (A[i].lo ^ B[j].lo) | (A[i].hi ^ B[j].hi); int w = __builtin_popcount(s2);
            if (w < dmin) dmin = w;
            if (w == wa) sA[na++] = s2; else if (w == wb) sB[nb++] = s2; else if (mode == 24 && w == 12) sC[nc++] = s2;
        }
        if (dmin != wa) { printf("id=%s res=ERROR min_distance_%d\n", id, dmin); fflush(stdout); continue; }
        memset(forb8bm, 0, 1u << (n - 3)); memset(forb12bm, 0, 1u << (n - 3));
        if (mode == 24) {
            for (long i = 0; i < na; i++) { u32 s2 = sA[i]; setbm(forb8bm, s2);
                for (u32 a = s2; a; a &= a - 1) { u32 y = a & -a; for (int b = 0; b < n; b++) if (!((s2 >> b) & 1)) setbm(forb8bm, (s2 & ~y) | (1u << b)); } }
            for (long i = 0; i < nb; i++) { u32 s2 = sB[i];
                for (u32 a = s2; a; a &= a - 1) { u32 a1 = a & -a; for (u32 b = a & (a - 1); b; b &= b - 1) setbm(forb8bm, s2 & ~a1 & ~(b & -b)); } }
            for (long i = 0; i < nc; i++) setbm(forb12bm, sC[i]);
        } else {
            for (long i = 0; i < na; i++) { u32 s2 = sA[i];
                for (u32 a = s2; a; a &= a - 1) { u32 a1 = a & -a; for (u32 b = a & (a - 1); b; b &= b - 1) setbm(forb8bm, s2 & ~a1 & ~(b & -b)); } }
            for (long i = 0; i < nb; i++) setbm(forb12bm, sB[i]);
        }
        char extra[256] = "";
        uint64_t hp = 0; int planted = 0;
        if (getenv("PLANT")) {
            planted = 1;
            int p0[32]; for (int i = 0; i < n; i++) p0[i] = i;
            rnd_seed((u64)atol(getenv("PLANT")) + (u64)li);
            for (int i = n - 1; i > 0; i--) { int j = (int)(rnd64() % (u64)(i + 1)); int t = p0[i]; p0[i] = p0[j]; p0[j] = t; }
            int nclr = 0;
            for (int b = 0; b < nblk; b++) { u32 m = blk[b], im = 0; while (m) { int pq = __builtin_ctz(m); m &= m - 1; im |= 1u << p0[pq]; } if (isforbset(btype[b], im)) { clrbm(btype[b] ? forb12bm : forb8bm, im); nclr++; } }
            u32 Bp[16]; for (int i = 0; i < nsrcb; i++) { u32 m = srcbasis[i], im = 0; while (m) { int pq = __builtin_ctz(m); m &= m - 1; im |= 1u << p0[pq]; } Bp[i] = im; }
            hp = code_hash(Bp, nsrcb, n);
            /* is the planted labelling in normal form? (it should essentially never be) */
            snprintf(extra, sizeof extra, "planted_hash=%016llx planted_cleared=%d", (unsigned long long)hp, nclr);
        }
        if (getenv("DUMPF")) {   /* BUILD-TIME TOOL ONLY: write the (possibly PLANT-cleared) forbidden families as raw
                                    2^24-bit bitmaps (byte m>>3, bit m&7), the layout read by csp5p's F mode */
            char fn[600]; FILE *fd;
            snprintf(fn, sizeof fn, "%s_f8.bin", getenv("DUMPF")); fd = fopen(fn, "wb"); fwrite(forb8bm, 1, 1u << (n - 3), fd); fclose(fd);
            snprintf(fn, sizeof fn, "%s_f12.bin", getenv("DUMPF")); fd = fopen(fn, "wb"); fwrite(forb12bm, 1, 1u << (n - 3), fd); fclose(fd);
        }
        long nf[2]; build_tables(nf);
        double prep = wallnow() - t0;
        run_instance();
        if (planted) { int pf = 0; for (long i = 0; i < nhashlist; i++) if (hashlist[i] == hp) pf = 1;
            size_t L = strlen(extra); snprintf(extra + L, sizeof extra - L, " planted_found=%d", pf); }
        print_result(id, wallnow() - t0, (double)(clock() - c0) / CLOCKS_PER_SEC, prep, na / 3, nb / 3, nc / 3, nf, extra);
    }
    return 0;
}
