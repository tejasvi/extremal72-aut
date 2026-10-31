// Level-wise exhaustive search for the C2 x C2 instances produced by lwprep.py.
// Variables are grouped by Gram row (level).  At a node all variables of levels < t are assigned; the k_t
// level-t variables v are enumerated as a bitset of 2^k_t children.  Every constraint of level t has syndrome
// s = s0 + L v (s0 from the assigned variables); children with s in Bad are removed, either by enumerating all
// children (Gray code) or by solving L v = b + s0 for each bad b and removing the coset v0 + ker L.
// Usage: lwe INSTANCE [SPLITLEVEL NPART PART]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <signal.h>
#include <unistd.h>
typedef uint64_t u64;
typedef unsigned __int128 u128;
static inline int par128(u128 x) { return (__builtin_popcountll((u64)x) + __builtin_popcountll((u64)(x >> 64))) & 1; }
static void die(const char *m) { fprintf(stderr, "%s\n", m); exit(1); }

typedef struct {
    int lv, wt, m, nbad;
    u128 fm[16]; int fc[16];          // syndrome forms (over all variables) and constants
    u128 lowm[16];                     // masks restricted to variables below the level
    u64 *badbm;                        // bitmap of bad syndromes (2^m bits)
    int *bad;                          // list of bad syndromes
    // level-t part
    int kt; uint32_t col[32];          // column j: syndrome contribution of level variable j (m bits)
    int method;                        // 0 = enumerate children, 1 = solve per bad syndrome
    int rank; int pivc[16]; uint32_t T[16]; uint32_t Z[16]; int nz;   // RREF data: pivot columns, transforms, zero-row checks
    int kdim; uint32_t kb[32];         // kernel basis
    // translated-base-bitmap method (method 3): image basis of L (syndrome space), cosets of Im L
    int tb;                            // 1 if method 3 available
    int irank; int ipiv[16]; uint32_t ivec[16]; uint32_t ipre[16];   // reduced image basis: ivec (m-bit), pivot bit, preimage (kt-bit)
    int ncos; int cbits[16];           // non-pivot syndrome coordinates (coset index bits)
    u64 *base;                         // ncos bitmaps of 2^kt bits each
} Con;

static int N, NLEV, NC; static int vstart[40]; static Con *C; static int lstart[41]; static int *ORD;
static u128 asg;
static long long nodes[40], kids[40], nsol = 0;
static int SPL = -1, NPART = 1, PART = 0; static long long splitcnt = 0;
static u64 *alive[40];
static long PROBES = 0; static double est[41]; static unsigned long long rs = 0x9E3779B97F4A7C15ULL;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double probe_w; static int probe_mode = 0;

static volatile sig_atomic_t stopflag = 0;
// ---- LTS symmetry (lex-leader on transported syndromes), see symprep.py ----
static int SYM = 0, SM = 0, SC0 = -1, SNE = 0; static int *scanon = NULL; static int *sent_c = NULL; static uint32_t *sent_rows = NULL;
static long long symprune[40];
static int syndrome_of(int c);
static void onsig(int sg) { (void)sg; stopflag = 1; }
static void read_sym(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open sym");
    if (fscanf(f, "%d %d %d", &SM, &SC0, &SNE) != 3) die("sym hdr");
    scanon = malloc(sizeof(int) << SM);
    for (int i = 0; i < (1 << SM); i++) if (fscanf(f, "%d", &scanon[i]) != 1) die("sym canon");
    sent_c = malloc(sizeof(int) * (SNE + 1)); sent_rows = malloc(sizeof(uint32_t) * (SNE + 1) * SM);
    for (int e = 0; e < SNE; e++) { if (fscanf(f, "%d", &sent_c[e]) != 1) die("sym ent");
        for (int j = 0; j < SM; j++) { unsigned x; if (fscanf(f, "%u", &x) != 1) die("sym row"); sent_rows[e * SM + j] = x; } }
    fclose(f); SYM = 1;
}
static void read_inst(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open");
    if (fscanf(f, "%d %d %d", &N, &NLEV, &NC) != 3) die("hdr");
    if (N > 128 || NLEV > 38) die("size");
    for (int t = 0; t <= NLEV; t++) if (fscanf(f, "%d", &vstart[t]) != 1) die("vstart");
    C = calloc(NC, sizeof(Con));
    for (int c = 0; c < NC; c++) {
        Con *X = &C[c];
        if (fscanf(f, "%d %d %d %d", &X->lv, &X->wt, &X->m, &X->nbad) != 4) die("con");
        if (X->m > 16) die("m>16");
        for (int s = 0; s < X->m; s++) {
            char hx[64]; if (fscanf(f, "%63s %d", hx, &X->fc[s]) != 2) die("form");
            u128 v = 0; for (char *q = hx; *q; q++) { int dv = (*q <= '9') ? *q - '0' : ((*q | 32) - 'a' + 10); v = (v << 4) | (u128)dv; }
            X->fm[s] = v;
        }
        int nb = ((1 << X->m) + 63) / 64; X->badbm = calloc(nb, sizeof(u64)); X->bad = malloc(sizeof(int) * (X->nbad + 1));
        for (int k = 0; k < X->nbad; k++) { int b; if (fscanf(f, "%d", &b) != 1) die("bad"); X->bad[k] = b; X->badbm[b >> 6] |= 1ULL << (b & 63); }
    }
    fclose(f);
    // level starts (constraints sorted by level)
    int c = 0;
    for (int t = 0; t <= NLEV; t++) { while (c < NC && C[c].lv < t) c++; lstart[t] = c; }
    lstart[NLEV] = NC;
    for (int k = 0; k < NC - 1; k++) if (C[k].lv > C[k + 1].lv) die("constraints not sorted");
    // precompute level parts
    for (int k = 0; k < NC; k++) {
        Con *X = &C[k]; int t = X->lv; int kt = vstart[t + 1] - vstart[t]; X->kt = kt;
        if (kt > 30) die("kt>30");
        u128 lowmask = (vstart[t] == 0) ? 0 : ((((u128)1) << vstart[t]) - 1);
        for (int s = 0; s < X->m; s++) {
            X->lowm[s] = X->fm[s] & lowmask;
            u128 hi = X->fm[s] >> vstart[t];
            if (vstart[t + 1] < 128 && (X->fm[s] >> vstart[t + 1]) != 0) die("form uses variables above its level");
            for (int j = 0; j < kt; j++) if ((hi >> j) & 1) X->col[j] |= 1u << s;
        }
        // RREF of L (m rows x kt cols): rows as kt-bit vectors with transform (m-bit)
        uint32_t R[16], Tr[16]; int m = X->m;
        for (int s = 0; s < m; s++) { R[s] = 0; for (int j = 0; j < kt; j++) if ((X->col[j] >> s) & 1) R[s] |= 1u << j; Tr[s] = 1u << s; }
        int r = 0; int pc[16];
        for (int j = 0; j < kt && r < m; j++) {
            int p = -1; for (int s = r; s < m; s++) if ((R[s] >> j) & 1) { p = s; break; }
            if (p < 0) continue;
            uint32_t tmp = R[p]; R[p] = R[r]; R[r] = tmp; tmp = Tr[p]; Tr[p] = Tr[r]; Tr[r] = tmp;
            for (int s = 0; s < m; s++) if (s != r && ((R[s] >> j) & 1)) { R[s] ^= R[r]; Tr[s] ^= Tr[r]; }
            pc[r] = j; r++;
        }
        X->rank = r; X->nz = 0;
        for (int i = 0; i < r; i++) { X->pivc[i] = pc[i]; X->T[i] = Tr[i]; }
        for (int s = r; s < m; s++) X->Z[X->nz++] = Tr[s];
        // kernel basis: for each free column f: v = e_f + sum_{i} R[i]_f e_{pivc[i]}
        X->kdim = 0; uint32_t pivmask = 0; for (int i = 0; i < r; i++) pivmask |= 1u << pc[i];
        for (int fcol = 0; fcol < kt; fcol++) if (!((pivmask >> fcol) & 1)) {
            uint32_t v = 1u << fcol;
            for (int i = 0; i < r; i++) if ((R[i] >> fcol) & 1) v |= 1u << pc[i];
            X->kb[X->kdim++] = v;
        }
        double costA = (double)(1ULL << kt), costB = (double)X->nbad * ((double)(1ULL << X->kdim) + 4.0);
        X->method = (r == 0) ? 2 : (costB < costA ? 1 : 0);
        X->tb = 0; X->base = NULL;
        if (r > 0) {
            // image basis: columns col[j] (m-bit) -> reduced basis with preimages
            int ir = 0; uint32_t iv[16], ip[16]; int pv[16];
            for (int j = 0; j < kt; j++) {
                uint32_t v = X->col[j], pre = 1u << j;
                for (int q = 0; q < ir; q++) if ((v >> pv[q]) & 1) { v ^= iv[q]; pre ^= ip[q]; }
                if (!v) continue;
                int pb = __builtin_ctz(v);
                for (int q = 0; q < ir; q++) if ((iv[q] >> pb) & 1) { iv[q] ^= v; ip[q] ^= pre; }
                iv[ir] = v; ip[ir] = pre; pv[ir] = pb; ir++;
            }
            X->irank = ir; for (int q = 0; q < ir; q++) { X->ivec[q] = iv[q]; X->ipre[q] = ip[q]; X->ipiv[q] = pv[q]; }
            int nc = 0; uint32_t pmask = 0; for (int q = 0; q < ir; q++) pmask |= 1u << pv[q];
            for (int b = 0; b < m; b++) if (!((pmask >> b) & 1)) X->cbits[nc++] = b;
            long ncos = 1L << nc; long words = ((1L << kt) + 63) / 64;
            if (ncos * words * 8 <= 65536) {
                X->ncos = (int)ncos; X->base = calloc(ncos * words, sizeof(u64));
                for (long ci2 = 0; ci2 < ncos; ci2++) {
                    uint32_t crep = 0; for (int q = 0; q < nc; q++) if ((ci2 >> q) & 1) crep |= 1u << X->cbits[q];
                    // base_c = { v : L v ^ crep in Bad }
                    u64 *B = X->base + ci2 * words;
                    int sv = (int)crep;
                    for (long v = 0; v < (1L << kt); v++) {
                        if (v) { int j = __builtin_ctzl(v); sv ^= X->col[j]; }
                        long g = v ^ (v >> 1);
                        if ((X->badbm[sv >> 6] >> (sv & 63)) & 1) B[g >> 6] |= 1ULL << (g & 63);
                    }
                }
                X->tb = 1;
            }
        }
    }
}

static inline int syn0(const Con *X) {
    int s0 = 0;
    for (int s = 0; s < X->m; s++) s0 |= (par128(X->lowm[s] & asg) ^ X->fc[s]) << s;
    return s0;
}

static const u64 TMASK[6] = {0x5555555555555555ULL, 0x3333333333333333ULL, 0x0F0F0F0F0F0F0F0FULL,
                              0x00FF00FF00FF00FFULL, 0x0000FFFF0000FFFFULL, 0x00000000FFFFFFFFULL};
// out[i] = bitmap translated by XOR with d:  out bit (v ^ d) = in bit v
static inline void xor_translate(u64 *out, const u64 *in, int nw, uint32_t d) {
    int hi = (int)(d >> 6);
    for (int i = 0; i < nw; i++) out[i ^ hi] = in[i];
    for (int j = 0; j < 6; j++) if ((d >> j) & 1) {
        int sh = 1 << j; u64 M = TMASK[j];
        for (int i = 0; i < nw; i++) { u64 w = out[i]; out[i] = ((w & M) << sh) | ((w >> sh) & M); }
    }
}
static int ordkey_cmp(const void *a, const void *b) {
    const Con *x = &C[*(const int *)a], *y = &C[*(const int *)b];
    // method 2 first (no level variables), then larger reachable-bad fraction (lower weight), then higher rank
    int mx = x->method == 2 ? 0 : 1, my = y->method == 2 ? 0 : 1;
    if (mx != my) return mx - my;
    if (x->wt != y->wt) return x->wt - y->wt;
    return y->rank - x->rank;
}
static void make_order(void) {
    ORD = malloc(sizeof(int) * NC);
    for (int c = 0; c < NC; c++) ORD[c] = c;
    for (int t = 0; t < NLEV; t++) qsort(ORD + lstart[t], lstart[t + 1] - lstart[t], sizeof(int), ordkey_cmp);
}
static int syndrome_of(int c) {
    const Con *X = &C[c]; int sv = 0;
    for (int q = 0; q < X->m; q++) sv |= (par128(X->fm[q] & asg) ^ X->fc[q]) << q;
    return sv;
}
static int sym_reject(int t) {   // 1 = prune this node (all variables of levels < t are assigned)
    if (t == 0 || C[SC0].lv >= t) return 0;
    int s0 = syndrome_of(SC0);
    if (C[SC0].lv == t - 1 && scanon[s0] != s0) return 1;
    for (int e = 0; e < SNE; e++) {
        int c = sent_c[e]; if (C[c].lv != t - 1) continue;
        int su = syndrome_of(c), tr = 0;
        for (int j = 0; j < SM; j++) tr |= (__builtin_popcount(sent_rows[e * SM + j] & (uint32_t)su) & 1) << j;
        if (scanon[tr] < s0) return 1;
    }
    return 0;
}
static void search(int t) {
    if (t == NLEV) {
        if (SYM && sym_reject(t)) { symprune[t]++; return; }
        nsol++;
        printf("SOLUTION %016llx%016llx\n", (unsigned long long)(asg >> 64), (unsigned long long)asg); fflush(stdout);
        return;
    }
    nodes[t]++;
    if (stopflag) return;
    if (SYM && sym_reject(t)) { symprune[t]++; return; }
    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }
    int kt = vstart[t + 1] - vstart[t];
    long nch = 1L << kt; int nw = (int)((nch + 63) / 64);
    u64 *A = alive[t];
    for (int i = 0; i < nw; i++) A[i] = ~0ULL;
    if (nch % 64) A[nw - 1] = (1ULL << (nch % 64)) - 1;
    int listmode = 0; int nlist = 0; uint32_t list[64];
    for (int ci = lstart[t]; ci < lstart[t + 1]; ci++) {
        const Con *X = &C[ORD[ci]];
        int s0 = syn0(X);
        if (listmode) {
            if (X->method == 2) { if ((X->badbm[s0 >> 6] >> (s0 & 63)) & 1) return; continue; }
            int nl = 0;
            for (int q = 0; q < nlist; q++) {
                uint32_t v = list[q]; int sv = s0;
                while (v) { int j = __builtin_ctz(v); v &= v - 1; sv ^= X->col[j]; }
                if (!((X->badbm[sv >> 6] >> (sv & 63)) & 1)) list[nl++] = list[q];
            }
            nlist = nl; if (!nlist) return;
            continue;
        }
        if (X->method == 2) {            // fully determined by lower levels
            if ((X->badbm[s0 >> 6] >> (s0 & 63)) & 1) return;
            continue;
        }
        if (X->tb) {
            // reduce s0 modulo Im L: s0 ^ L v0 = crep (coset rep), then bad children = base_crep translated by v0
            uint32_t sv = (uint32_t)s0, v0 = 0;
            for (int q = 0; q < X->irank; q++) if ((sv >> X->ipiv[q]) & 1) { sv ^= X->ivec[q]; v0 ^= X->ipre[q]; }
            long ci2 = 0; for (int q = 0; q < X->ncos; q++) { if (q >= 16) break; }
            for (int q = 0; (1L << q) < X->ncos; q++) if ((sv >> X->cbits[q]) & 1) ci2 |= 1L << q;
            u64 tmp[128];
            const u64 *Bm = X->base + ci2 * nw;
            if (nch < 64) { u64 w = Bm[0]; u64 o = w; uint32_t d = v0; o = w;
                for (int j = 0; j < 6; j++) if ((d >> j) & 1) { int sh = 1 << j; u64 M = TMASK[j]; o = ((o & M) << sh) | ((o >> sh) & M); }
                A[0] &= ~o; }
            else { xor_translate(tmp, Bm, nw, v0); for (int i = 0; i < nw; i++) A[i] &= ~tmp[i]; }
        } else if (X->method == 0) {
            int s = s0;
            for (long v = 0; v < nch; v++) {
                if (v) { int j = __builtin_ctzl(v); s ^= X->col[j]; }
                long g = v ^ (v >> 1);    // Gray code index whose syndrome is s
                if ((X->badbm[s >> 6] >> (s & 63)) & 1) A[g >> 6] &= ~(1ULL << (g & 63));
            }
        } else {
            for (int k = 0; k < X->nbad; k++) {
                int r = X->bad[k] ^ s0; int ok = 1;
                for (int z = 0; z < X->nz; z++) if (__builtin_popcount(X->Z[z] & r) & 1) { ok = 0; break; }
                if (!ok) continue;
                uint32_t v0 = 0;
                for (int i = 0; i < X->rank; i++) if (__builtin_popcount(X->T[i] & r) & 1) v0 |= 1u << X->pivc[i];
                uint32_t v = v0;
                long nk = 1L << X->kdim;
                for (long q = 0; q < nk; q++) {
                    if (q) { int j = __builtin_ctzl(q); v ^= X->kb[j]; }
                    A[v >> 6] &= ~(1ULL << (v & 63));
                }
            }
        }
        // early exit if nothing alive; switch to list mode when few children remain
        long cnt = 0; for (int i = 0; i < nw; i++) cnt += __builtin_popcountll(A[i]);
        if (!cnt) return;
        if (cnt <= 48) {
            listmode = 1; nlist = 0;
            for (int i = 0; i < nw; i++) { u64 b = A[i]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; list[nlist++] = (uint32_t)(((long)i << 6) + j); } }
        }
    }
    if (listmode) {   // rebuild the alive bitmap from the list
        for (int i = 0; i < nw; i++) A[i] = 0;
        for (int q = 0; q < nlist; q++) A[list[q] >> 6] |= 1ULL << (list[q] & 63);
    }
    u128 clearmask = ~(((((u128)1) << kt) - 1) << vstart[t]);
    if (probe_mode) {
        long cnt = 0; for (int i = 0; i < nw; i++) cnt += __builtin_popcountll(A[i]);
        if (!cnt) return;
        long pick = (long)(rnd64() % (unsigned long long)cnt);
        for (int i = 0; i < nw; i++) { long c = __builtin_popcountll(A[i]); if (pick < c) { u64 b = A[i]; for (long q = 0; q < pick; q++) b &= b - 1; long v = ((long)i << 6) + __builtin_ctzll(b);
                    probe_w *= (double)cnt; est[t + 1] += probe_w;
                    asg = (asg & clearmask) | (((u128)v) << vstart[t]); search(t + 1); asg &= clearmask; return; } pick -= c; }
        return;
    }
    for (int i = 0; i < nw; i++) {
        u64 bits = A[i];
        while (bits) {
            int j = __builtin_ctzll(bits); bits &= bits - 1;
            long v = ((long)i << 6) + j;
            kids[t]++;
            asg = (asg & clearmask) | (((u128)v) << vstart[t]);
            search(t + 1);
        }
    }
    asg &= clearmask;
}

int main(int argc, char **argv) {
    if (argc < 2) die("usage: lwe INSTANCE [SPLITLEVEL NPART PART]");
    read_inst(argv[1]);
    make_order();
    { const char *sf = getenv("SYMFILE"); if (sf) read_sym(sf); }
    if (argc > 4) { SPL = atoi(argv[2]); NPART = atoi(argv[3]); PART = atoi(argv[4]); }
    int kmax = 0; for (int t = 0; t < NLEV; t++) { int k = vstart[t + 1] - vstart[t]; if (k > kmax) kmax = k; }
    for (int t = 0; t < NLEV; t++) alive[t] = malloc(sizeof(u64) * (((1L << kmax) + 63) / 64 + 1));
    time_t t0 = time(NULL); asg = 0;
    { const char *pe = getenv("PROBES"); if (pe) PROBES = atol(pe); }
    if (PROBES > 0) {
        probe_mode = 1;
        for (long p = 0; p < PROBES; p++) { probe_w = 1.0; est[0] += 1.0; asg = 0; search(0); }
        double tot = 0; printf("PROBE estimate (%ld probes):", PROBES);
        for (int t = 0; t <= NLEV; t++) { printf(" %d:%.3g", t, est[t] / PROBES); tot += est[t] / PROBES; }
        printf("\nTOTAL nodes ~ %.3e\n", tot); return 0;
    }
    signal(SIGTERM, onsig); signal(SIGALRM, onsig); { const char *al = getenv("ALARM"); if (al) alarm(atoi(al)); }
    search(0);
    if (stopflag) printf("STOPPED (partial counts)\n");
    printf("DONE lwe nsol %lld time %lds split %d part %d/%d N %d\n", nsol, (long)(time(NULL) - t0), SPL, PART, NPART, N);
    for (int t = 0; t < NLEV; t++) printf("LEVEL %d kt %d ncons %d nodes %lld kids %lld symprune %lld\n", t, vstart[t + 1] - vstart[t], lstart[t + 1] - lstart[t], nodes[t], kids[t], symprune[t]);
    printf("SYMPRUNE at leaves %lld\n", symprune[NLEV]);
    return 0;
}
