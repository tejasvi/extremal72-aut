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
} Con;

static int N, NLEV, NC; static int vstart[40]; static Con *C; static int lstart[41];
static u128 asg;
static long long nodes[40], kids[40], nsol = 0;
static int SPL = -1, NPART = 1, PART = 0; static long long splitcnt = 0;
static u64 *alive[40];

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
    }
}

static inline int syn0(const Con *X) {
    int s0 = 0;
    for (int s = 0; s < X->m; s++) s0 |= (par128(X->lowm[s] & asg) ^ X->fc[s]) << s;
    return s0;
}

static void search(int t) {
    if (t == NLEV) {
        nsol++;
        printf("SOLUTION %016llx%016llx\n", (unsigned long long)(asg >> 64), (unsigned long long)asg); fflush(stdout);
        return;
    }
    nodes[t]++;
    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }
    int kt = vstart[t + 1] - vstart[t];
    long nch = 1L << kt; int nw = (int)((nch + 63) / 64);
    u64 *A = alive[t];
    for (int i = 0; i < nw; i++) A[i] = ~0ULL;
    if (nch % 64) A[nw - 1] = (1ULL << (nch % 64)) - 1;
    for (int c = lstart[t]; c < lstart[t + 1]; c++) {
        const Con *X = &C[c];
        int s0 = syn0(X);
        if (X->method == 2) {            // fully determined by lower levels
            if ((X->badbm[s0 >> 6] >> (s0 & 63)) & 1) return;
            continue;
        }
        if (X->method == 0) {
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
        // early exit if nothing alive
        int any = 0; for (int i = 0; i < nw; i++) if (A[i]) { any = 1; break; }
        if (!any) return;
    }
    u128 clearmask = ~(((((u128)1) << kt) - 1) << vstart[t]);
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
    if (argc > 4) { SPL = atoi(argv[2]); NPART = atoi(argv[3]); PART = atoi(argv[4]); }
    int kmax = 0; for (int t = 0; t < NLEV; t++) { int k = vstart[t + 1] - vstart[t]; if (k > kmax) kmax = k; }
    for (int t = 0; t < NLEV; t++) alive[t] = malloc(sizeof(u64) * (((1L << kmax) + 63) / 64 + 1));
    time_t t0 = time(NULL); asg = 0;
    search(0);
    printf("DONE lwe nsol %lld time %lds split %d part %d/%d N %d\n", nsol, (long)(time(NULL) - t0), SPL, PART, NPART, N);
    for (int t = 0; t < NLEV; t++) printf("LEVEL %d kt %d ncons %d nodes %lld kids %lld\n", t, vstart[t + 1] - vstart[t], lstart[t + 1] - lstart[t], nodes[t], kids[t]);
    return 0;
}
