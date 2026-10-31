// Level-wise exhaustive search for the C2 x C2 instances produced by lwprep.py.
// Variables are grouped by Gram row (level).  At a node all variables of levels < t are assigned; the k_t
// level-t variables v are enumerated as a bitset of 2^k_t children.  Every constraint of level t has syndrome
// s = s0 + L v (s0 from the assigned variables); children with s in Bad are removed, either by enumerating all
// children (Gray code) or by solving L v = b + s0 for each bad b and removing the coset v0 + ker L.
// Usage: lwe INSTANCE [SPLITLEVEL NPART PART]
// lwe11 (c2opt/alg stream, 2026-10-22, release rc13) = lwe10 with a new level filter; same search tree, same pruning decisions,
// byte-identical LEVEL/DONE/SOLUTION output (validated against lwe8, see c2opt/alg/ALG_REPORT.md):
//  - s0 of all constraints of a level as one uint16 vector, kept incrementally along the path (4-bit chunk row
//    tables per lower level, stamped by the node identity nid[e]);
//  - bad children of a constraint = base bitmap of the coset of s0 modulo Im L, XOR-translated by v0 with VPERMB
//    (bytes) + GF2P8AFFINEQB (bits within a byte); per-lane tables in fixed-stride arenas; if 2^m * max(8, bitmap
//    bytes) <= DCAP (16 KB) a direct table s0 -> bad-children bitmap instead; emptiness tested every second
//    constraint; kt <= 8 uses exact-width loads and ops (64-bit word, XMM, YMM), kt = 9 one ZMM, kt = 10 (two ZMMs)
//    has its own loop; kt >= 11 keeps a generic multi-ZMM loop with list mode; kt > 16 uses the lwe10 code;
//  - LTSH: transports as split tables, syndromes of symmetry words read from the s0 vectors, group elements whose
//    components are all trivial (the identity) skipped, only orbit words completed at level t-1 transported, older
//    ties recorded per level on the path (lh_reject2, same decision as lh_reject), lh skipped at levels where it
//    cannot return 1.
//  - bulk LTSH at the parent: children rejected because a word new at their level transports below s0 are found
//    with translate lanes (bad set { s : canon[t_u(s)] < s0 } on the word's syndromes, rebuilt when s0 changes) and
//    counted as nodes/lhprune without entering search (off in probe mode and with SYMFILE/LTSFILE).
//    rc8: the bulk tables are cached per s0 value (deep key words); the split level's parent counts split-rejected
//    children itself (exact counts; off with SYMFILE/LTSFILE or a symmetry test at the split level).
//    rc9: arena layout and dedicated loops also for kt = 11, 12 (four / eight ZMMs).
//    rc11: optional LTSBFILE (bit-granular LTS, c2struct's struct/src/lwe10b.c prototype): a comparand g whose
//    transported key-word syndrome is not yet fully determined is compared MSB first on its determined leading
//    bits; the node is pruned when that prefix is already smaller than s0.  Trigger lists per level; LWE11CHECK
//    compares with the prototype's full loop.  Without LTSBFILE nothing changes.
//    rc13: less per-node overhead, same decisions: the wide filter path in its own function and per-level static
//    buffers for the bulk masks (no 17-32 KB stack frames per node), bit-granular test bits
//    and decisions cached per epoch, and children of levels without node tests go straight to the filter.
//    The same pass marks children with a tie among those words; for all others lh_reject2 skips the new-word loop.
//  Needs AVX-512 F/BW/VL/VBMI/VPOPCNTDQ and GFNI; main (baseline ISA) checks this first and refuses cleanly (rc7).  LWE11CHECK=1 verifies every fast node (s0
//  vectors, alive sets, symmetry-word syndromes, bulk/tie claims, lh_reject2 = lh_reject) against a direct computation.  LWE11OFF=1 uses the lwe10 level filter.
// lwe10 = lwe9 + branch-free inner loops (list filter, coset reduction, one-word translation); same decisions.
// lwe9 = lwe8 with the same search and the same pruning decisions, made faster by caching:
//  - base syndromes s0 of level-t constraints: part from levels < t-2 cached per grandparent node (epoch nid[t-2]),
//    plus table lookups for the level t-2 and t-1 values (tables U2, U1);
//  - list mode: child syndrome contributions L v from a per-constraint table V (kt <= 12);
//  - LTSH: syndromes of key/orbit words cached per ancestor node (epoch nid[lv+1]); transported canonical values
//    of orbit words cached likewise.  Debug/validation: identical LEVEL lines to lwe8 on the same input.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <signal.h>
#include <unistd.h>
#include <immintrin.h>
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
    // lwe9 caches: s0 = A ^ U2[x_{t-2}] ^ U1[x_{t-1}];  A = fc ^ parities over levels < t-2 (epoch nid[t-2])
    int usetab; u128 lowA[16]; uint16_t *U1, *U2; int Aval; unsigned long long Ast;
    uint16_t *V;                       // V[v] = L v for kt <= 12 (list mode)
} Con;

static int N, NLEV, NC; static int vstart[40]; static Con *C; static int lstart[41]; static int *ORD;
static u128 asg;
static long long nodes[40], kids[40], nsol = 0;
static int SPL = -1, NPART = 1, PART = 0; static long long splitcnt = 0;
static u64 *alive[40]; static u64 *tmpbuf;
static long PROBES = 0; static double est[41]; static unsigned long long rs = 0x9E3779B97F4A7C15ULL;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double probe_w; static int probe_mode = 0;

static volatile sig_atomic_t stopflag = 0;
// ---- LTS symmetry (lex-leader on transported syndromes), see symprep.py ----
static int SYM = 0, SM = 0, SC0 = -1, SNE = 0; static int *scanon = NULL; static int *sent_c = NULL; static uint32_t *sent_rows = NULL;
static long long symprune[40];
// ---- LTS-r: lex-leader on the key (s_w0, ..., s_w{r-1}) over all g in G (see symprep2.py) ----
static int LR = 0, LRr = 0, LRnG = 0; static int LRc[16], LRm[16];
static int *LRgc = NULL; static uint16_t *LRrows = NULL;
static int *LRls = NULL, *LRlg = NULL, *LRlj = NULL;
static long long ltsprune[41];
// ---- hybrid LTS-r (LTSH, see symprep3.py) ----
static int LH = 0, LHr, LHm0, LHc0, LHnO, LHnS0, LHnG, LHncls; static int LHc[16], LHm[16];
static int *LHcanon, *LHh, *LHclsOf, *LHJs, *LHJ, *LHmul, *LHuc, *LHcomp, *LHgc;
static uint16_t *LHut, *LHgt; static unsigned *LHtrig; static long long lhprune[41];
static int *SCval = NULL; static unsigned *SCstamp = NULL; static unsigned SCcur = 0;
static unsigned long long nid[42], NIDC = 0;                     // node identity per level (epoch)
static int *EPval = NULL; static unsigned long long *EPst = NULL;  // syndromes cached by epoch nid[lv+1]
static int *UAval = NULL, *UCval = NULL; static unsigned long long *UCst = NULL;   // per orbit word u: a, canon(a)
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

static inline int syn0_plain(const Con *X) {
    int s0 = 0;
    for (int s = 0; s < X->m; s++) s0 |= (par128(X->lowm[s] & asg) ^ X->fc[s]) << s;
    return s0;
}
static inline int lvval(int l) { return (int)((asg >> vstart[l]) & ((((u128)1) << (vstart[l + 1] - vstart[l])) - 1)); }
static inline int syn0(Con *X) {
    if (!X->usetab) return syn0_plain(X);
    int t = X->lv;
    if (X->Ast != nid[t - 2]) {
        int a = 0; for (int s = 0; s < X->m; s++) a |= (par128(X->lowA[s] & asg) ^ X->fc[s]) << s;
        X->Aval = a; X->Ast = nid[t - 2];
    }
    return X->Aval ^ X->U2[lvval(t - 2)] ^ X->U1[lvval(t - 1)];
}
static void build_tables(void) {
    long bytes = 0;
    for (int c = 0; c < NC; c++) {
        Con *X = &C[c]; int t = X->lv; X->usetab = 0; X->U1 = X->U2 = NULL; X->V = NULL; X->Ast = ~0ULL;
        if (X->kt <= 12) {
            long n = 1L << X->kt; X->V = malloc(sizeof(uint16_t) * n); X->V[0] = 0;
            for (long v = 1; v < n; v++) { int j = __builtin_ctzl(v); X->V[v] = X->V[v & (v - 1)] ^ (uint16_t)X->col[j]; }
            bytes += n * 2;
        }
        if (t < 2) continue;
        int k1 = vstart[t] - vstart[t - 1], k2 = vstart[t - 1] - vstart[t - 2];
        if (k1 > 13 || k2 > 13) continue;
        u128 mA = (vstart[t - 2] == 0) ? 0 : ((((u128)1) << vstart[t - 2]) - 1);
        for (int s = 0; s < X->m; s++) X->lowA[s] = X->fm[s] & mA;
        X->U1 = malloc(sizeof(uint16_t) << k1); X->U2 = malloc(sizeof(uint16_t) << k2);
        uint32_t c1[16] = {0}, c2[16] = {0};   // per level variable j: syndrome column (m bits)
        for (int s = 0; s < X->m; s++) {
            for (int j = 0; j < k1; j++) if ((X->fm[s] >> (vstart[t - 1] + j)) & 1) c1[j] |= 1u << s;
            for (int j = 0; j < k2; j++) if ((X->fm[s] >> (vstart[t - 2] + j)) & 1) c2[j] |= 1u << s;
        }
        X->U1[0] = 0; for (long v = 1; v < (1L << k1); v++) { int j = __builtin_ctzl(v); X->U1[v] = X->U1[v & (v - 1)] ^ (uint16_t)c1[j]; }
        X->U2[0] = 0; for (long v = 1; v < (1L << k2); v++) { int j = __builtin_ctzl(v); X->U2[v] = X->U2[v & (v - 1)] ^ (uint16_t)c2[j]; }
        bytes += (2L << k1) + (2L << k2); X->usetab = 1;
    }
    if (getenv("LWE9VERB")) fprintf(stderr, "lwe9 tables: %.1f MB\n", bytes / 1048576.0);
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
static int syndrome_of(int c);
static void read_ltsr(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open ltsr");
    char tag[16]; if (fscanf(f, "%15s %d %d", tag, &LRr, &LRnG) != 3 || strcmp(tag, "LTSR")) die("ltsr hdr");
    if (LRr < 1 || LRr > 16) die("ltsr r");
    for (int i = 0; i < LRr; i++) if (fscanf(f, "%d %d", &LRc[i], &LRm[i]) != 2 || LRm[i] > 16) die("ltsr key");
    LRgc = malloc(sizeof(int) * (size_t)LRnG * LRr); LRrows = calloc((size_t)LRnG * LRr * 16, sizeof(uint16_t));
    for (int g = 0; g < LRnG; g++) for (int i = 0; i < LRr; i++) {
        if (fscanf(f, "%d", &LRgc[(size_t)g * LRr + i]) != 1) die("ltsr gc");
        for (int j = 0; j < LRm[i]; j++) { unsigned x; if (fscanf(f, "%u", &x) != 1) die("ltsr row"); LRrows[((size_t)g * LRr + i) * 16 + j] = (uint16_t)x; }
    }
    fclose(f);
    // static triggers: component i comparable at level max(lv(c_{g,i}), lv(c_i)) + 1; prefix j comparable at T_j
    int *cnt = calloc(NLEV + 2, sizeof(int));
    int *Tj = malloc(sizeof(int) * (LRr + 1));
    for (int pass = 0; pass < 2; pass++) {
        if (pass == 1) { LRls = calloc(NLEV + 3, sizeof(int)); for (int t = 0; t <= NLEV + 1; t++) LRls[t + 1] = LRls[t] + cnt[t];
                         LRlg = malloc(sizeof(int) * (LRls[NLEV + 2] + 1)); LRlj = malloc(sizeof(int) * (LRls[NLEV + 2] + 1)); memset(cnt, 0, sizeof(int) * (NLEV + 2)); }
        for (int g = 0; g < LRnG; g++) {
            Tj[0] = 0;
            for (int j = 1; j <= LRr; j++) {
                int a = C[LRgc[(size_t)g * LRr + j - 1]].lv, b = C[LRc[j - 1]].lv;
                int lv = (a > b ? a : b) + 1; Tj[j] = Tj[j - 1] > lv ? Tj[j - 1] : lv;
            }
            for (int j = 1; j <= LRr; j++) {
                if (j < LRr && Tj[j + 1] == Tj[j]) continue;      // only the longest prefix per trigger level
                int t = Tj[j]; if (t > NLEV) t = NLEV;
                if (pass == 0) cnt[t]++;
                else { int pos = LRls[t] + cnt[t]++; LRlg[pos] = g; LRlj[pos] = j; }
            }
        }
    }
    // deterministic shuffle within each level (order does not affect which nodes are pruned)
    unsigned long long st = 0x2545F4914F6CDD1DULL;
    for (int t = 0; t <= NLEV; t++) for (int a = LRls[t + 1] - 1; a > LRls[t]; a--) {
        st ^= st << 13; st ^= st >> 7; st ^= st << 17;
        int b = LRls[t] + (int)(st % (unsigned long long)(a - LRls[t] + 1));
        int x = LRlg[a]; LRlg[a] = LRlg[b]; LRlg[b] = x; x = LRlj[a]; LRlj[a] = LRlj[b]; LRlj[b] = x;
    }
    SCval = malloc(sizeof(int) * NC); SCstamp = calloc(NC, sizeof(unsigned));
    free(cnt); free(Tj); LR = 1;
}
static inline int syn_cached(int c);
static void read_ltsh(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open ltsh");
    char tag[16];
    if (fscanf(f, "%15s %d %d %d %d %d %d %d", tag, &LHr, &LHm0, &LHc0, &LHnO, &LHnS0, &LHnG, &LHncls) != 8 || strcmp(tag, "LTSH")) die("ltsh hdr");
    for (int i = 0; i < LHr; i++) if (fscanf(f, "%d %d", &LHc[i], &LHm[i]) != 2 || LHm[i] > 16) die("ltsh key");
    int M = 1 << LHm0;
    LHcanon = malloc(sizeof(int) * M); LHh = malloc(sizeof(int) * M); LHclsOf = malloc(sizeof(int) * M);
    for (int i = 0; i < M; i++) if (fscanf(f, "%d", &LHcanon[i]) != 1) die("ltsh canon");
    for (int i = 0; i < M; i++) if (fscanf(f, "%d", &LHh[i]) != 1) die("ltsh h");
    for (int i = 0; i < M; i++) LHclsOf[i] = -1;
    LHJs = malloc(sizeof(int) * (LHncls + 1)); int cap = 1024, used = 0; LHJ = malloc(sizeof(int) * cap);
    for (int k = 0; k < LHncls; k++) {
        int c, n; if (fscanf(f, "%d %d", &c, &n) != 2) die("ltsh cls"); LHclsOf[c] = k; LHJs[k] = used;
        for (int q = 0; q < n; q++) { if (used >= cap) { cap *= 2; LHJ = realloc(LHJ, sizeof(int) * cap); } if (fscanf(f, "%d", &LHJ[used]) != 1) die("ltsh J"); used++; }
    }
    LHJs[LHncls] = used;
    LHmul = malloc(sizeof(int) * (size_t)LHnS0 * LHnS0);
    for (size_t i = 0; i < (size_t)LHnS0 * LHnS0; i++) if (fscanf(f, "%d", &LHmul[i]) != 1) die("ltsh mul");
    LHuc = malloc(sizeof(int) * LHnO); LHut = calloc((size_t)LHnO * 16, sizeof(uint16_t)); LHcomp = malloc(sizeof(int) * (size_t)LHnO * LHnS0);
    for (int u = 0; u < LHnO; u++) {
        if (fscanf(f, "%d", &LHuc[u]) != 1) die("ltsh uc");
        for (int j = 0; j < LHm0; j++) { unsigned x; if (fscanf(f, "%u", &x) != 1) die("ltsh ut"); LHut[(size_t)u * 16 + j] = (uint16_t)x; }
        for (int q = 0; q < LHnS0; q++) if (fscanf(f, "%d", &LHcomp[(size_t)u * LHnS0 + q]) != 1) die("ltsh comp");
    }
    if (LHr > 1) {
        LHgc = malloc(sizeof(int) * (size_t)LHnG * (LHr - 1)); LHgt = calloc((size_t)LHnG * (LHr - 1) * 16, sizeof(uint16_t));
        LHtrig = calloc(LHnG, sizeof(unsigned));
        for (int g = 0; g < LHnG; g++) for (int i = 1; i < LHr; i++) {
            size_t o = (size_t)g * (LHr - 1) + (i - 1);
            if (fscanf(f, "%d", &LHgc[o]) != 1) die("ltsh gc");
            for (int j = 0; j < LHm[i]; j++) { unsigned x; if (fscanf(f, "%u", &x) != 1) die("ltsh gt"); LHgt[o * 16 + j] = (uint16_t)x; }
            int a = C[LHgc[o]].lv, b = C[LHc[i]].lv; int L = (a > b ? a : b) + 1; if (L > 31) die("ltsh level");
            LHtrig[g] |= 1u << L;
        }
    }
    fclose(f);
    if (!SCval) { SCval = malloc(sizeof(int) * NC); SCstamp = calloc(NC, sizeof(unsigned)); }
    EPval = malloc(sizeof(int) * NC); EPst = malloc(sizeof(unsigned long long) * NC); for (int c = 0; c < NC; c++) EPst[c] = ~0ULL;
    UAval = malloc(sizeof(int) * LHnO); UCval = malloc(sizeof(int) * LHnO); UCst = malloc(sizeof(unsigned long long) * LHnO);
    for (int u = 0; u < LHnO; u++) UCst[u] = ~0ULL;
    LH = 1;
}
static inline int tr16(const uint16_t *R, int m, int s) { int x = 0; for (int q = 0; q < m; q++) x |= (__builtin_popcount(R[q] & (unsigned)s) & 1) << q; return x; }
static inline int syn_fast(int c);
static uint16_t **TGlo, **TGhi, **TUlo, **TUhi;   // lwe11: transports T_{g,i} and t_u as split tables (lo byte, high bits)
static unsigned char *gskip, *ctriv;              // g whose components are all trivial (always equal); trivial component
static inline int syn_ep(int c) {          // syndrome of constraint c (all its variables assigned), cached per ancestor
    unsigned long long e = nid[C[c].lv + 1];
    if (EPst[c] != e) { EPst[c] = e; EPval[c] = syn_fast(c); }
    return EPval[c];
}
static int lh_check_g(int g, int t) {      // components 1..r-1, lexicographic; 1 = transported key smaller (prune)
    for (int i = 1; i < LHr; i++) {
        size_t o = (size_t)g * (LHr - 1) + (i - 1);
        int c = LHgc[o];
        if (C[c].lv > t - 1 || C[LHc[i]].lv > t - 1) return 0;
        if (ctriv[o]) continue;                     // c = c_i and T = I: always equal
        int sc = syn_ep(c);
        int x = TGlo[o][sc & 255] ^ TGhi[o][sc >> 8], y = syn_ep(LHc[i]);
        if (x < y) return 1;
        if (x > y) return 0;
    }
    return 0;
}
static int lh_reject(int t) {
    int lv0 = C[LHc0].lv;
    if (t - 1 < lv0) return 0;
    int s0 = syn_ep(LHc0);
    if (lv0 == t - 1 && LHcanon[s0] != s0) return 1;
    int cls = LHclsOf[s0]; if (cls < 0) return 1;   /* cannot happen: s0 canonical */
    int Jn = LHJs[cls + 1] - LHJs[cls]; const int *J = &LHJ[LHJs[cls]];
    for (int u = 0; u < LHnO; u++) {
        int cu = LHuc[u]; int lu = C[cu].lv > lv0 ? C[cu].lv : lv0;
        if (lu > t - 1) continue;
        int newu = (lu == t - 1);
        int a, ca;
        unsigned long long e = nid[lu + 1];
        if (UCst[u] == e) { a = UAval[u]; ca = UCval[u]; }
        else {
            if (u == 0) a = s0; else { int su = syn_ep(cu); a = TUlo[u][su & 255] ^ TUhi[u][su >> 8]; }
            ca = LHcanon[a]; UAval[u] = a; UCval[u] = ca; UCst[u] = e;
        }
        if (ca < s0) { if (newu) return 1; continue; }
        if (ca != s0 || LHr < 2) continue;
        int h = LHh[a];
        for (int q = 0; q < Jn; q++) {
            int sig = LHmul[(size_t)h * LHnS0 + J[q]];
            int g = LHcomp[(size_t)u * LHnS0 + sig];
            if (gskip[g]) continue;                 // lh_check_g(g, .) is always 0
            if (!newu && !((LHtrig[g] >> t) & 1)) continue;
            if (lh_check_g(g, t)) return 1;
        }
    }
    return 0;
}
// rc11: bit-granular LTS (LTSBFILE written by c2struct's mkltsb.py / ltsblib.py; decisions as struct/src/lwe10b.c).
// File: 'LTSB nG m0 c0', then per g in G one line 'lv(c_u) F_0 c_0 L_0 ... F_{m0-1} c_{m0-1} L_{m0-1}': bit j of the
// transported key-word syndrome s_w0(B^g) is parity(F_j & x) ^ c_j, determined once all variables of levels <= L_j are
// assigned; lv(c_u) is the level of the constraint of u = g w0.  At a node of level t (> lv0), every g with
// lv(c_u) > t-1 is compared MSB first on its determined leading bits with s0 = s_w0(B); the node is pruned when that
// prefix is already smaller.  Then s_w0(B^g) < s0 for every completion, and since canon0 is the S0-orbit minimum
// (canon0(a) <= a) the LTSH test prunes every completion once c_u is complete: the leaf set does not change.
// A comparand whose determined prefix did not grow at level t-1 gives the same answer as at the parent (no prune), so
// level t only tests its trigger list LBtg[LBts[t] .. LBts[t+1]-1] (at t = lv0+1: every comparand with a prefix).
static int LB = 0, LBnG = 0, LBm0 = 0; static int *LBlu = NULL; static u128 *LBF = NULL; static unsigned char *LBc = NULL;
static signed char *LBlev = NULL; static long long lbprune[41], lbchecked = 0;
static uint8_t *LBval = NULL; static unsigned long long *LBvst = NULL;   // rc13: bit (g, j) cached while LBvst = nid[L_j + 1]
static int *LBglv = NULL; static unsigned long long *LBgst = NULL;      // rc13: g compared greater on bits of levels <= LBglv[g]: valid while LBgst = nid[LBglv + 1]
static int LBts[42], *LBtg = NULL; static unsigned char lbact[42];
static int lb_lvl(u128 v) {               // level of the highest variable of a form, -1 for 0, -2 if beyond the variables
    if (!v) return -1;
    const u64 hi = (u64)(v >> 64), lo = (u64)v; const int hb = hi ? 127 - __builtin_clzll(hi) : 63 - __builtin_clzll(lo);
    for (int t = 0; t < NLEV; t++) if (vstart[t] <= hb && hb < vstart[t + 1]) return t;
    return -2;
}
static void read_ltsb(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("open ltsb");
    char tag[16]; int c0;
    if (fscanf(f, "%15s %d %d %d", tag, &LBnG, &LBm0, &c0) != 4 || strcmp(tag, "LTSB")) die("ltsb hdr");
    if (!LH || LBm0 != LHm0 || c0 != LHc0 || LBnG != LHnG) die("ltsb does not match the LTSH file");
    LBlu = malloc(sizeof(int) * LBnG); LBF = malloc(sizeof(u128) * (size_t)LBnG * LBm0);
    LBc = malloc((size_t)LBnG * LBm0); LBlev = malloc((size_t)LBnG * LBm0);
    LBval = calloc((size_t)LBnG * LBm0 + 1, 1); LBvst = calloc((size_t)LBnG * LBm0 + 1, sizeof(unsigned long long));
    LBglv = calloc((size_t)LBnG + 1, sizeof(int)); LBgst = calloc((size_t)LBnG + 1, sizeof(unsigned long long));
    if (!LBlu || !LBF || !LBc || !LBlev) die("alloc");
    for (int g = 0; g < LBnG; g++) {
        if (fscanf(f, "%d", &LBlu[g]) != 1 || LBlu[g] < 0 || LBlu[g] >= NLEV) die("ltsb lu");
        for (int j = 0; j < LBm0; j++) {
            char hx[64]; int c, l; if (fscanf(f, "%63s %d %d", hx, &c, &l) != 3) die("ltsb bit");
            u128 v = 0; for (char *q = hx; *q; q++) { int dv = (*q <= '9') ? *q - '0' : ((*q | 32) - 'a' + 10); v = (v << 4) | (u128)dv; }
            if ((c != 0 && c != 1) || l < -1 || l >= NLEV) die("ltsb bit value");
            if (lb_lvl(v) != l) die("ltsb: a bit's level differs from the level of its form's highest variable");
            size_t o = (size_t)g * LBm0 + j; LBF[o] = v; LBc[o] = (unsigned char)c; LBlev[o] = (signed char)l;
        }
    }
    fclose(f);
    for (int a = 0; a < (1 << LHm0); a++) if (LHcanon[a] > a) die("ltsb: canon0 is not the orbit minimum");
    LB = 1;
}
static int lb_plen(int g, int t) {         // leading (MSB-first) bits of comparand g determined at level t
    int p = 0; for (int j = LBm0 - 1; j >= 0 && LBlev[(size_t)g * LBm0 + j] <= t - 1; j--) p++; return p;
}
static void build_lb(void) {
    const int lv0 = C[LHc0].lv; int n = 0;
    LBtg = malloc(sizeof(int) * ((size_t)LBnG * (NLEV + 1) + 1)); if (!LBtg) die("alloc");
    for (int t = 0; t <= NLEV; t++) {
        LBts[t] = n; lbact[t] = 0;
        if (t - 1 < lv0 || t >= NLEV) continue;
        for (int g = 0; g < LBnG; g++) {
            if (LBlu[g] <= t - 1) continue;
            const int p = lb_plen(g, t), pp = (t == lv0 + 1) ? 0 : lb_plen(g, t - 1);
            if (p > pp) LBtg[n++] = g;
        }
        lbact[t] = (unsigned char)(n > LBts[t]);
    }
    LBts[NLEV + 1] = n;
}
static int lb_reject_full(int t) {         // struct/src/lwe10b.c's lb_reject (every comparand): LWE11CHECK reference
    int lv0 = C[LHc0].lv;
    if (t - 1 < lv0) return 0;
    int s0 = syn_ep(LHc0);
    for (int g = 0; g < LBnG; g++) {
        if (LBlu[g] <= t - 1) continue;
        for (int j = LBm0 - 1; j >= 0; j--) {
            size_t o = (size_t)g * LBm0 + j;
            if (LBlev[o] > t - 1) break;
            int b = par128(LBF[o] & asg) ^ LBc[o], sb = (s0 >> j) & 1;
            if (b < sb) return 1;
            if (b > sb) break;
        }
    }
    return 0;
}
static int lb_reject_fast(int t) {         // same decision as lb_reject_full, over the trigger list of level t
    const int s0 = syn_ep(LHc0), lv0 = C[LHc0].lv;
    for (int q = LBts[t]; q < LBts[t + 1]; q++) {
        const int g = LBtg[q]; const size_t o0 = (size_t)g * LBm0;
        if (LBglv[g] + 1 <= t && LBgst[g] == nid[LBglv[g] + 1]) continue;   // rc13: g already compared greater at this ancestor
                                                   // (nid[e] identifies the current path only for e <= t)
        int dl = lv0;                              // the comparison so far depends on s0 and on the bits read
        for (int j = LBm0 - 1; j >= 0; j--) {
            const size_t o = o0 + j;
            const int lv = LBlev[o];
            if (lv > t - 1) break;
            int b;                                 // rc13: the bit depends on levels <= lv only, cached per ancestor of level lv + 1
            if (LBvst[o] == nid[lv + 1]) b = LBval[o];
            else { b = par128(LBF[o] & asg) ^ LBc[o]; LBval[o] = (uint8_t)b; LBvst[o] = nid[lv + 1]; }
            if (lv > dl) dl = lv;
            const int sb = (s0 >> j) & 1;
            if (b < sb) return 1;
            if (b > sb) { LBglv[g] = dl; LBgst[g] = nid[dl + 1]; break; }   // same outcome everywhere below that ancestor
        }
    }
    return 0;
}
static inline int syn_cached(int c) {
    if (SCstamp[c] != SCcur) { SCstamp[c] = SCcur; SCval[c] = syndrome_of(c); }
    return SCval[c];
}
static int ltsr_reject(int t) {
    if (t > NLEV) return 0;
    SCcur++;
    for (int e = LRls[t]; e < LRls[t + 1]; e++) {
        int g = LRlg[e], j = LRlj[e];
        for (int i = 0; i < j; i++) {
            int su = syn_cached(LRgc[(size_t)g * LRr + i]);
            const uint16_t *R = &LRrows[((size_t)g * LRr + i) * 16];
            int x = 0; for (int q = 0; q < LRm[i]; q++) x |= (__builtin_popcount(R[q] & (unsigned)su) & 1) << q;
            int y = syn_cached(LRc[i]);
            if (x < y) return 1;
            if (x > y) break;
        }
    }
    return 0;
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
// ---- lwe11: fast level filter (AVX-512 VBMI + GFNI) ----
// Per level t the constraints get lanes in processing order: rank-0 constraints first (whole node), then the
// translate constraints, then the rest (checked child by child).  s0 of every lane is one uint16 vector
// P[t] = fc ^ sum_{l<t} row_l(x_l), kept along the path: P[e] = P[e-1] ^ (chunk rows of x_{e-1}), stamped nid[e].
// Translate constraint: bad children of s0 = base[coset(s0)] XOR-translated by v0(s0), where
// s0 = crep ^ L v0 (reduction modulo Im L); (coset, v0) = cvlo[s0 & 255] ^ cvhi[s0 >> 8] (the reduction is linear).
typedef struct {
    const uint32_t *cvlo, *cvhi;      // (coset << 16) | v0
    const uint8_t *base;              // one bitmap of 'stride' = 1 << sh bytes per coset of Im L (+64 bytes padding)
    const uint16_t *vlo, *vhi;        // L x = vlo[x & 255] ^ vhi[x >> 8] (list mode, kt >= 10)
    int sh;
} FC;
typedef struct {
    int on, kt, nbytes, nz, nwords, nc, npad, nr0, ntr, vec, thr;
    int ndir, de; uint8_t *DT; uint32_t *DOFF; int arena;   // arena: arena layout usable (built, or no translate lanes)   // last ndir translate lanes use direct tables: bad(s) = DT[DOFF[i] + s*de]
    int *cid;                         // constraint index per lane
    FC *fc;                           // translate records for lanes nr0 .. nr0+ntr-1
    uint16_t *PB; unsigned long long *PBst;
    uint16_t *chunk[40][4];           // chunk[l][q]: 16 rows of npad lanes (bits 4q..4q+3 of x_l)
    u64 *allm;                        // nz*8 words: low 2^kt bits set
    uint32_t *CVL, *CVH; int hs;      // arena layout (kt <= 9): cv(s) = CVL[i*64 + (s & 63)] ^ CVH[i*hs + (s >> 6)] = (arena offset << 9) | v0
    uint8_t *AR;                      // base bitmaps, lane regions aligned to their power-of-2 size
} LV;
#ifndef OPT_ARENA
#define OPT_ARENA 1
#endif
#ifndef OPT_NARROW
#define OPT_NARROW 1
#endif
#ifndef OPT_UNROLL2
#define OPT_UNROLL2 1
#endif
#ifndef DCAP
#define DCAP 16384           // direct table if 2^m * max(8, bitmap bytes) <= DCAP
#endif
#ifndef TRCAP
#define TRCAP 32768           // translate method if (cosets of Im L) * bitmap bytes <= TRCAP, else child by child
#endif
#ifndef VECCAP
#define VECCAP (4L << 20)     // s0 vector chain for a level if its tables need <= VECCAP bytes ...
#endif
#ifndef VECBUDGET
#define VECBUDGET (24L << 20) // ... and the total stays <= VECBUDGET
#endif
#define OPT_IDX(e) _mm512_xor_si512(IOTA, _mm512_set1_epi8((char)(((e) >> 3) & 63)))   // VPERMB index for byte shift (e >> 3) & 63
static LV LVL[40];
static int nchunk[41];
static u64 xv[41];                    // value of level l on the current path
static unsigned char lhact[42];       // lh_reject can return 1 at level t
static __m512i IOTA;
static u64 AFF[8];
static int CHECK = 0, LH2 = 1;                 // LWE11CHECK: verify s0 vectors and alive sets against a direct computation
static long long fastnodes = 0, checknodes = 0;
static int *laneOf; static uint16_t **SVlo, **SVhi; static unsigned char *need_sv;

static void *amalloc(size_t n) { void *p = aligned_alloc(64, (n + 63) / 64 * 64 + 64); if (!p) die("alloc"); memset(p, 0, (n + 63) / 64 * 64 + 64); return p; }
static inline uint32_t colL(const Con *X, int l, int j) {   // syndrome column of variable j of level l
    uint32_t v = 0; for (int s = 0; s < X->m; s++) v |= (uint32_t)((X->fm[s] >> (vstart[l] + j)) & 1) << s; return v;
}
static uint32_t reduce_cv(const Con *X, uint32_t s0) {      // (coset index << 16) | v0 with s0 = crep ^ L v0
    uint32_t sv = s0, v0 = 0;
    for (int q = 0; q < X->irank; q++) if ((sv >> X->ipiv[q]) & 1) { sv ^= X->ivec[q]; v0 ^= X->ipre[q]; }
    uint32_t ci = 0; for (int q = 0; q < X->m - X->irank; q++) if ((sv >> X->cbits[q]) & 1) ci |= 1u << q;
    return (ci << 16) | v0;
}
static void build_fast(void) {
    need_sv = calloc(NC + 1, 1);
    for (int j = 0; j < 8; j++) { u64 A = 0; for (int i = 0; i < 8; i++) A |= (u64)(1u << (i ^ j)) << (8 * (7 - i)); AFF[j] = A; }
    { uint8_t io[64]; for (int i = 0; i < 64; i++) io[i] = (uint8_t)i; IOTA = _mm512_loadu_si512(io); }
    for (int l = 0; l <= NLEV; l++) { int k = (l < NLEV) ? vstart[l + 1] - vstart[l] : 0; nchunk[l] = (k + 3) / 4; }
    const char *thr = getenv("LWE11THR");
    long tbytes = 0, vbytes = 0; long vbudget = VECBUDGET;
    for (int t = 0; t < NLEV; t++) {
        LV *L = &LVL[t]; memset(L, 0, sizeof(LV));
        int kt = vstart[t + 1] - vstart[t];
        if (kt > 16 || getenv("LWE11OFF")) continue;
        L->kt = kt; L->nbytes = kt >= 3 ? 1 << (kt - 3) : 1; L->nz = L->nbytes >= 64 ? L->nbytes / 64 : 1;
        L->nwords = kt >= 6 ? 1 << (kt - 6) : 1;
        L->thr = thr ? atoi(thr) : (L->nz <= 2 ? 0 : 4 * L->nz); if (L->thr > 48) L->thr = 48;
        int nc = lstart[t + 1] - lstart[t]; L->nc = nc; L->npad = (nc + 31) / 32 * 32; if (L->npad == 0) L->npad = 32;
        L->cid = malloc(sizeof(int) * (nc + 1)); L->fc = calloc(nc + 1, sizeof(FC));
        // classify in ORD order: rank 0, translate (base fits), rest
        int *cls = malloc(sizeof(int) * (nc + 1));
        for (int i = 0; i < nc; i++) {
            Con *X = &C[ORD[lstart[t] + i]];
            if (X->rank == 0) cls[i] = 0;
            else { long ncos = 1L << (X->m - X->irank); cls[i] = (ncos * L->nbytes <= TRCAP) ? 1 : 3; }
            if (cls[i] == 1 && L->nz == 1 && OPT_ARENA && (1L << X->m) * (L->nbytes < 8 ? 8 : L->nbytes) <= DCAP) cls[i] = 2;   // direct table
        }
        int pos = 0;
        for (int k = 0; k < 4; k++) for (int i = 0; i < nc; i++) if (cls[i] == k) L->cid[pos++] = ORD[lstart[t] + i];
        L->nr0 = 0; L->ntr = 0; L->ndir = 0;
        for (int i = 0; i < nc; i++) { if (cls[i] == 0) L->nr0++; if (cls[i] == 1 || cls[i] == 2) L->ntr++; if (cls[i] == 2) L->ndir++; }
        free(cls);
        for (int i = L->nr0; i < L->nr0 + L->ntr; i++) {
            Con *X = &C[L->cid[i]]; FC *F = &L->fc[i];
            int m = X->m; long ns = 1L << m; int sh = 0; while ((1 << sh) < L->nbytes) sh++;
            F->sh = sh;
            long nh = ns > 64 ? ns >> 6 : 1;
            uint32_t *lo = amalloc(sizeof(uint32_t) * 64), *hi = amalloc(sizeof(uint32_t) * nh);
            #define CVOFF(v) ((((v) >> 16) << (16 + sh)) | ((v) & 0xFFFF))
            for (long s = 0; s < 64; s++) lo[s] = (s < ns) ? CVOFF(reduce_cv(X, (uint32_t)s)) : 0;
            hi[0] = 0; for (long h = 1; h < nh; h++) hi[h] = CVOFF(reduce_cv(X, (uint32_t)(h << 6)));
            for (long s = 0; s < ns; s++) if ((lo[s & 63] ^ hi[s >> 6]) != CVOFF(reduce_cv(X, (uint32_t)s))) die("cv not linear");
            F->cvlo = lo; F->cvhi = hi; tbytes += 4 * (64 + nh);
            long ncos = 1L << (m - X->irank);
            uint8_t *B = amalloc((size_t)ncos * L->nbytes + 64);
            for (long ci = 0; ci < ncos; ci++) {
                uint32_t crep = 0; for (int q = 0; q < m - X->irank; q++) if ((ci >> q) & 1) crep |= 1u << X->cbits[q];
                uint8_t *b = B + ci * L->nbytes; uint32_t sv = crep;
                for (long v = 0; v < (1L << kt); v++) {
                    if (v) sv ^= X->col[__builtin_ctzl(v)];
                    long g = v ^ (v >> 1);
                    if ((X->badbm[sv >> 6] >> (sv & 63)) & 1) b[g >> 3] |= (uint8_t)(1u << (g & 7));
                }
            }
            F->base = B; tbytes += ncos * L->nbytes;
            if (kt >= 10) {
                uint16_t *vl = malloc(sizeof(uint16_t) * 256), *vh = malloc(sizeof(uint16_t) * (1 << (kt - 8)));
                for (int x = 0; x < 256; x++) { uint32_t a = 0; for (int j = 0; j < 8 && j < kt; j++) if ((x >> j) & 1) a ^= X->col[j]; vl[x] = (uint16_t)a; }
                for (int x = 0; x < (1 << (kt - 8)); x++) { uint32_t a = 0; for (int j = 0; j < kt - 8; j++) if ((x >> j) & 1) a ^= X->col[8 + j]; vh[x] = (uint16_t)a; }
                F->vlo = vl; F->vhi = vh;
            }
        }
        L->allm = amalloc(sizeof(u64) * L->nz * 8);
        for (long v = 0; v < (1L << kt); v++) L->allm[v >> 6] |= 1ULL << (v & 63);
        L->arena = (L->ntr == 0);
        if (L->nz <= 8 && L->ntr > 0) {        // arena layout for kt <= 12 (VB = v0 bits: 9 for kt <= 9, else kt)
            int hs = 1; long *sz = malloc(sizeof(long) * (nc + 1)); int *ord = malloc(sizeof(int) * (nc + 1)); int no = 0;
            for (int i = L->nr0; i < L->nr0 + L->ntr; i++) {
                const Con *X = &C[L->cid[i]]; long h = X->m > 6 ? 1L << (X->m - 6) : 1; if (h > hs) hs = (int)h;
                long need = (1L << (X->m - X->irank)) * L->nbytes, p2 = 1; while (p2 < need) p2 <<= 1; sz[i] = p2; ord[no++] = i;
            }
            for (int a = 0; a < no; a++) for (int b = a + 1; b < no; b++) if (sz[ord[b]] > sz[ord[a]]) { int x = ord[a]; ord[a] = ord[b]; ord[b] = x; }
            long cur = 0; long *off = malloc(sizeof(long) * (nc + 1));
            for (int a = 0; a < no; a++) { int i = ord[a]; off[i] = cur; cur += sz[i]; }
            const int VB = L->nz == 1 ? 9 : L->nz == 2 ? 10 : L->nz == 4 ? 11 : 12; const uint32_t VM = (1u << VB) - 1;
            if (cur >= (1L << (32 - VB))) { free(sz); free(ord); free(off); goto noarena; }
            L->AR = amalloc(cur + 128); L->hs = hs;
            L->CVL = amalloc(sizeof(uint32_t) * 64 * (size_t)nc); L->CVH = amalloc(sizeof(uint32_t) * (size_t)hs * nc);
            for (int i = L->nr0; i < L->nr0 + L->ntr; i++) {
                const Con *X = &C[L->cid[i]]; const FC *F = &L->fc[i]; long ns = 1L << X->m;
                memcpy(L->AR + off[i], F->base, (size_t)(1L << (X->m - X->irank)) * L->nbytes);
                for (int a = 0; a < 64; a++) { uint32_t e = F->cvlo[a]; L->CVL[(size_t)i * 64 + a] = (((uint32_t)off[i] | (e >> 16)) << VB) | (e & VM); }
                for (long h = 0; h < (ns > 64 ? ns >> 6 : 1); h++) { uint32_t e = F->cvhi[h]; L->CVH[(size_t)i * hs + h] = (e >> 16) << VB | (e & VM); }
                for (long q = 0; q < ns; q++) {   // verify the arena entry reproduces the FC entry
                    uint32_t e1 = F->cvlo[q & 63] ^ F->cvhi[q >> 6], e2 = L->CVL[(size_t)i * 64 + (q & 63)] ^ L->CVH[(size_t)i * hs + (q >> 6)];
                    if ((e2 >> VB) != (uint32_t)off[i] + (e1 >> 16) || (e2 & VM) != (e1 & 0xFFFF)) die("arena entry");
                }
            }
            free(sz); free(ord); free(off);
            L->arena = 1;
        }
        noarena:;
        if (L->ndir > 0) {
            int de = L->nbytes < 8 ? 8 : L->nbytes; L->de = de; long tot = 0;
            L->DOFF = amalloc(sizeof(uint32_t) * (size_t)nc);
            for (int i = L->nr0 + L->ntr - L->ndir; i < L->nr0 + L->ntr; i++) { L->DOFF[i] = (uint32_t)tot; tot += (1L << C[L->cid[i]].m) * de; }
            L->DT = amalloc(tot + 128);
            for (int i = L->nr0 + L->ntr - L->ndir; i < L->nr0 + L->ntr; i++) {
                const Con *X = &C[L->cid[i]];
                for (long s0 = 0; s0 < (1L << X->m); s0++) {
                    uint8_t *b = L->DT + L->DOFF[i] + s0 * de; uint32_t sv = (uint32_t)s0;
                    for (long v = 0; v < (1L << kt); v++) {
                        if (v) sv ^= X->col[__builtin_ctzl(v)];
                        long g = v ^ (v >> 1);
                        if ((X->badbm[sv >> 6] >> (sv & 63)) & 1) b[g >> 3] |= (uint8_t)(1u << (g & 7));
                    }
                }
            }
            tbytes += tot;
        }
        // s0 vector chain
        long need = 0; for (int l = 0; l < t; l++) need += (long)nchunk[l] * 16 * L->npad * 2;
        need += (long)(t + 1) * L->npad * 2;
        if (need <= VECCAP && vbytes + need <= vbudget) {
            L->vec = 1; vbytes += need;
            L->PB = amalloc(sizeof(uint16_t) * (size_t)(t + 1) * L->npad); L->PBst = calloc(t + 1, sizeof(unsigned long long));
            for (int i = 0; i < nc; i++) { const Con *X = &C[L->cid[i]]; uint32_t f = 0; for (int s = 0; s < X->m; s++) f |= (uint32_t)X->fc[s] << s; L->PB[i] = (uint16_t)f; }
            for (int l = 0; l < t; l++) {
                int k = vstart[l + 1] - vstart[l];
                for (int q = 0; q < nchunk[l]; q++) {
                    uint16_t *T = amalloc(sizeof(uint16_t) * 16 * L->npad); L->chunk[l][q] = T;
                    for (int i = 0; i < nc; i++) {
                        const Con *X = &C[L->cid[i]]; uint32_t cl[4];
                        for (int j = 0; j < 4; j++) cl[j] = (4 * q + j < k) ? colL(X, l, 4 * q + j) : 0;
                        for (int r = 0; r < 16; r++) { uint32_t a = 0; for (int j = 0; j < 4; j++) if ((r >> j) & 1) a ^= cl[j]; T[(size_t)r * L->npad + i] = (uint16_t)a; }
                    }
                }
            }
        }
        L->on = 1;
    }
    if (LH) {
        int lv0 = C[LHc0].lv;
        for (int t = 0; t <= NLEV; t++) {
            int a = 0;
            if (t - 1 >= lv0) {
                if (lv0 == t - 1) a = 1;
                for (int u = 0; u < LHnO; u++) { int lu = C[LHuc[u]].lv > lv0 ? C[LHuc[u]].lv : lv0; if (lu == t - 1) a = 1; }
                if (LHr >= 2) { if (t >= 32) a = 1; else for (int g = 0; g < LHnG; g++) if ((LHtrig[g] >> t) & 1) a = 1; }
            }
            lhact[t] = (unsigned char)a;
        }
        if (getenv("LWE11NOSKIP")) for (int t = 0; t <= NLEV; t++) lhact[t] = 1;
        // transports as split tables; trivial components / elements
        int nO = LHnO, nGo = LHr > 1 ? LHnG * (LHr - 1) : 0;
        TUlo = calloc(nO + 1, sizeof(uint16_t *)); TUhi = calloc(nO + 1, sizeof(uint16_t *));
        for (int u = 0; u < nO; u++) {
            int mi = C[LHuc[u]].m; long nh = mi > 8 ? 1L << (mi - 8) : 1;
            TUlo[u] = malloc(sizeof(uint16_t) * 256); TUhi[u] = malloc(sizeof(uint16_t) * nh);
            for (int b = 0; b < 256; b++) TUlo[u][b] = (uint16_t)tr16(&LHut[(size_t)u * 16], LHm0, b);
            for (long h = 0; h < nh; h++) TUhi[u][h] = (uint16_t)tr16(&LHut[(size_t)u * 16], LHm0, (int)(h << 8));
            need_sv[LHuc[u]] = 1;
        }
        TGlo = calloc(nGo + 1, sizeof(uint16_t *)); TGhi = calloc(nGo + 1, sizeof(uint16_t *));
        ctriv = calloc(nGo + 1, 1); gskip = calloc(LHnG + 1, 1);
        for (int g = 0; g < LHnG; g++) {
            int all = (LHr > 1);
            for (int i = 1; i < LHr; i++) {
                size_t o = (size_t)g * (LHr - 1) + (i - 1); int c = LHgc[o]; int mi = C[c].m; long nh = mi > 8 ? 1L << (mi - 8) : 1;
                TGlo[o] = malloc(sizeof(uint16_t) * 256); TGhi[o] = malloc(sizeof(uint16_t) * nh);
                for (int b = 0; b < 256; b++) TGlo[o][b] = (uint16_t)tr16(&LHgt[o * 16], LHm[i], b);
                for (long h = 0; h < nh; h++) TGhi[o][h] = (uint16_t)tr16(&LHgt[o * 16], LHm[i], (int)(h << 8));
                int triv = (c == LHc[i]); for (int j = 0; j < LHm[i]; j++) if (LHgt[o * 16 + j] != (1u << j)) triv = 0;
                ctriv[o] = (unsigned char)triv; if (!triv) all = 0;
                need_sv[c] = 1; need_sv[LHc[i]] = 1;
            }
            gskip[g] = (unsigned char)all;
            if (getenv("LWE11NOGSKIP")) gskip[g] = 0;
        }
        need_sv[LHc0] = 1;
        if (getenv("LWE11VERB")) { int ns = 0; for (int g = 0; g < LHnG; g++) ns += gskip[g]; fprintf(stderr, "lwe11: %d always-equal group elements skipped\n", ns); }
    }
    // L x tables for constraints whose syndromes the symmetry test reads (fast syndromes from the s0 vectors)
    laneOf = malloc(sizeof(int) * NC); for (int c = 0; c < NC; c++) laneOf[c] = -1;
    for (int t = 0; t < NLEV; t++) if (LVL[t].on) for (int i = 0; i < LVL[t].nc; i++) laneOf[LVL[t].cid[i]] = i;
    SVlo = calloc(NC, sizeof(uint16_t *)); SVhi = calloc(NC, sizeof(uint16_t *));
    for (int c = 0; c < NC; c++) if (need_sv[c] && laneOf[c] >= 0 && C[c].kt <= 16) {
        const Con *X = &C[c]; int kt = X->kt; long nh = kt > 8 ? 1L << (kt - 8) : 1;
        SVlo[c] = malloc(sizeof(uint16_t) * 256); SVhi[c] = malloc(sizeof(uint16_t) * nh);
        for (int x = 0; x < 256; x++) { uint32_t a = 0; for (int j = 0; j < 8 && j < kt; j++) if ((x >> j) & 1) a ^= X->col[j]; SVlo[c][x] = (uint16_t)a; }
        for (long x = 0; x < nh; x++) { uint32_t a = 0; for (int j = 0; j < kt - 8; j++) if ((x >> j) & 1) a ^= X->col[8 + j]; SVhi[c][x] = (uint16_t)a; }
    }
    if (getenv("LWE11VERB")) {
        fprintf(stderr, "lwe11: translate tables %.2f MB, s0 vector tables %.2f MB\n", tbytes / 1048576.0, vbytes / 1048576.0);
        for (int t = 0; t < NLEV; t++) { LV *L = &LVL[t]; fprintf(stderr, " L%d on %d kt %d nc %d r0 %d tr %d rest %d vec %d thr %d lhact %d\n", t, L->on, L->kt, L->nc, L->nr0, L->ntr, L->nc - L->nr0 - L->ntr, L->vec, L->thr, lhact[t]); }
    }
}
static inline const uint16_t *s0vec(LV *L, int t) {
    int e = t;
    while (e > 0 && L->PBst[e] != nid[e]) e--;
    const int np = L->npad;
    for (int f = e + 1; f <= t; f++) {
        const int l = f - 1, nq = nchunk[l]; const unsigned x = (unsigned)xv[l];
        const uint16_t *src = L->PB + (size_t)(f - 1) * np; uint16_t *dst = L->PB + (size_t)f * np;
        const uint16_t *r0 = nq > 0 ? L->chunk[l][0] + (size_t)(x & 15) * np : NULL;
        const uint16_t *r1 = nq > 1 ? L->chunk[l][1] + (size_t)((x >> 4) & 15) * np : NULL;
        const uint16_t *r2 = nq > 2 ? L->chunk[l][2] + (size_t)((x >> 8) & 15) * np : NULL;
        const uint16_t *r3 = nq > 3 ? L->chunk[l][3] + (size_t)((x >> 12) & 15) * np : NULL;
        for (int i = 0; i < np; i += 32) {
            __m512i a = _mm512_load_si512((const void *)(src + i));
            if (nq > 0) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r0 + i)));
            if (nq > 1) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r1 + i)));
            if (nq > 2) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r2 + i)));
            if (nq > 3) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r3 + i)));
            _mm512_store_si512((void *)(dst + i), a);
        }
        L->PBst[f] = nid[f];
    }
    return L->PB + (size_t)t * np;
}
static inline int syn_fast(int c) {   // syndrome of c from the s0 vector of its level on the current path
    const int l = C[c].lv; const LV *L = &LVL[l];
    if (SVlo[c] && L->vec) {
        const uint32_t x = (uint32_t)xv[l];
        int s = L->PB[(size_t)l * L->npad + laneOf[c]] ^ SVlo[c][x & 255] ^ SVhi[c][x >> 8];
        if (CHECK && (s != syndrome_of(c) || (l > 0 && L->PBst[l] != nid[l]))) { fprintf(stderr, "CHECK syn_fast mismatch c %d level %d\n", c, l); exit(3); }
        return s;
    }
    return syndrome_of(c);
}
static inline uint32_t lane_s0(LV *L, const uint16_t *S, int i) { return L->vec ? S[i] : (uint32_t)syn0(&C[L->cid[i]]); }
static inline int bad_child(const Con *X, uint32_t s0, uint32_t v) {
    uint32_t sv = s0; while (v) { sv ^= X->col[__builtin_ctz(v)]; v &= v - 1; }
    return (int)((X->badbm[sv >> 6] >> (sv & 63)) & 1);
}
static void check_node(LV *L, int t, const uint16_t *S, const u64 *alive, int dead) {   // LWE11CHECK
    checknodes++;
    if (L->vec) for (int i = 0; i < L->nc; i++) if (S[i] != (uint16_t)syn0_plain(&C[L->cid[i]])) { fprintf(stderr, "CHECK s0 mismatch level %d lane %d\n", t, i); exit(3); }
    static uint32_t s0d[8192];
    for (int i = 0; i < L->nc; i++) s0d[i] = (uint32_t)syn0_plain(&C[L->cid[i]]);
    for (long v = 0; v < (1L << L->kt); v++) {
        int ok = 1;
        for (int i = 0; i < L->nc && ok; i++) { const Con *X = &C[L->cid[i]]; if (bad_child(X, s0d[i], (uint32_t)v)) ok = 0; }
        int got = dead ? 0 : (int)((alive[v >> 6] >> (v & 63)) & 1);
        if (ok != got) { fprintf(stderr, "CHECK alive mismatch level %d child %ld: direct %d fast %d\n", t, v, ok, got); exit(3); }
    }
}

#ifdef PROFPC
#include <sys/time.h>
#include <ucontext.h>
static volatile int curlev = 0;
static unsigned long *pcbuf; static volatile long npc = 0; static int levhist[64];
static void onprof(int sg, siginfo_t *si, void *uc) { (void)sg; (void)si; if (npc < (1L << 22)) pcbuf[npc++] = (unsigned long)((ucontext_t *)uc)->uc_mcontext.gregs[REG_RIP]; levhist[curlev & 63]++; }
static void prof_start(void) { pcbuf = malloc(sizeof(unsigned long) << 22); struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = onprof; sa.sa_flags = SA_SIGINFO | SA_RESTART; sigaction(SIGPROF, &sa, NULL);
    struct itimerval it = {{0, 500}, {0, 500}}; setitimer(ITIMER_PROF, &it, NULL); }
static void prof_dump(void) { struct itimerval it = {{0, 0}, {0, 0}}; setitimer(ITIMER_PROF, &it, NULL);
    FILE *f = fopen(getenv("PROFOUT"), "w"); for (long i = 0; i < npc; i++) fprintf(f, "%lx\n", pcbuf[i]); fclose(f);
    long tot = 0; for (int l = 0; l < 64; l++) tot += levhist[l]; for (int l = 0; l < 64; l++) if (levhist[l]) fprintf(stderr, "PROF level %d: %.1f%%\n", l, 100.0 * levhist[l] / tot); }
#define SETLEV(t) (curlev = (t))
#else
#define SETLEV(t) ((void)0)
#endif
// lh_reject2: same decision as lh_reject.  Only orbit words completed at level t-1 ("new") are transported; an older
// word can matter only if it tied (canonical transported value = s0) when it was new, so ties are recorded per level
// on the current path and only their elements with a trigger at level t are compared.
static int lhnewn[42]; static int *lhnew[42];
static unsigned char newdone[42];
static int fsplit_ok = 0, presplit = 0;   // rc8: the split level's parent counts split-rejected children itself  // set by the parent's bulk loop: the child's new words have no tie (and none rejects)
static int tien[42]; static int *tieu[42], *tieh[42];   // ties recorded at level t (at most the new words of t)
static void build_lh2(void) {
    int lv0 = C[LHc0].lv;
    for (int t = 0; t <= NLEV + 1 && t < 42; t++) { lhnewn[t] = 0; lhnew[t] = malloc(sizeof(int) * (LHnO + 1)); tien[t] = 0; tieu[t] = malloc(sizeof(int) * (LHnO + 1)); tieh[t] = malloc(sizeof(int) * (LHnO + 1)); }
    for (int u = 0; u < LHnO; u++) { int lu = C[LHuc[u]].lv > lv0 ? C[LHuc[u]].lv : lv0; if (lu + 1 < 42) lhnew[lu + 1][lhnewn[lu + 1]++] = u; }
}
static int lh_reject2(int t) {
    int lv0 = C[LHc0].lv;
    if (t - 1 < lv0) return 0;
    int s0 = syn_ep(LHc0);
    if (lv0 == t - 1 && LHcanon[s0] != s0) return 1;
    int cls = LHclsOf[s0]; if (cls < 0) return 1;   /* cannot happen: s0 canonical */
    int Jn = LHJs[cls + 1] - LHJs[cls]; const int *J = &LHJ[LHJs[cls]];
    tien[t] = 0;
    const int nd = newdone[t]; newdone[t] = 0;
    if (nd && CHECK) { for (int k = 0; k < lhnewn[t]; k++) { int u = lhnew[t][k]; if (u == 0) continue; int su = syn_ep(LHuc[u]); int ca = LHcanon[TUlo[u][su & 255] ^ TUhi[u][su >> 8]];
            if (ca <= s0) { fprintf(stderr, "CHECK newdone mismatch level %d u %d\n", t, u); exit(3); } } }
    for (int k = 0; k < lhnewn[t] && !nd; k++) {
        int u = lhnew[t][k], a;
        if (u == 0) a = s0; else { int su = syn_ep(LHuc[u]); a = TUlo[u][su & 255] ^ TUhi[u][su >> 8]; }
        int ca = LHcanon[a];
        if (ca < s0) return 1;
        if (ca != s0 || LHr < 2) continue;
        int h = LHh[a];
        tieu[t][tien[t]] = u; tieh[t][tien[t]] = h; tien[t]++;
        for (int q = 0; q < Jn; q++) {
            int g = LHcomp[(size_t)u * LHnS0 + LHmul[(size_t)h * LHnS0 + J[q]]];
            if (gskip[g]) continue;
            if (lh_check_g(g, t)) return 1;
        }
    }
    if (LHr < 2 || t >= 32) { if (LHr >= 2 && t >= 32) die("lh2 level"); return 0; }
    for (int tp = lv0 + 1; tp < t; tp++) for (int k = 0; k < tien[tp]; k++) {
        int u = tieu[tp][k], h = tieh[tp][k];
        for (int q = 0; q < Jn; q++) {
            int g = LHcomp[(size_t)u * LHnS0 + LHmul[(size_t)h * LHnS0 + J[q]]];
            if (gskip[g] || !((LHtrig[g] >> t) & 1)) continue;
            if (lh_check_g(g, t)) return 1;
        }
    }
    return 0;
}
// Bulk LTSH at the parent.  For a child level tc with tc-1 > lv0 (so s0 = s_k0 is fixed below the parent), every
// orbit word u != 0 new at tc whose constraint cu has level tc-1 gives the bad set BU = { s : canon[t_u(s)] < s0 } on
// cu's syndromes.  A child whose cu-syndrome lies in BU is rejected by lh_reject2 (and lh_reject).  These children are
// found with the translate method (cu's cosets, base bitmaps for BU rebuilt when s0 changes) and counted as nodes and
// lhprune of level tc without entering search.  Off in probe mode and with SYMFILE/LTSFILE (order of tests).
typedef struct { int u, cu, lane; const FC *F; uint8_t *base, *tbase; long ncos; size_t off, sz; } BL;
static BL *blv[42]; static int nbl[42]; static int bls0[42];
// rc8: the BU bitmaps of all lanes of a level are one block per s0 value, cached (s0 is fixed below the key's level, so
// with a deep key word it changes at every node of level lv0+1); beyond BLCAP bytes a scratch block is rebuilt.
#ifndef BLCAP
#define BLCAP (48L << 20)
#endif
static uint8_t **blc[42], *blscr[42]; static size_t blsize[42], blbytes = 0; static int blscr0[42];
static unsigned char blfull[42];   // every word u != 0 new at tc is covered: children outside the tie mask skip the new-word loop
static void build_bulk(void) {
    const int lv0 = C[LHc0].lv;
    for (int tc = 0; tc < 42; tc++) { nbl[tc] = 0; bls0[tc] = -1; blv[tc] = NULL; }
    if (!LH || SYM || LR || LHr < 1 || getenv("LWE11NOBULK")) return;
    for (int tc = lv0 + 2; tc < NLEV && tc < 42; tc++) {
        LV *L = &LVL[tc - 1]; if (!L->on || !L->vec) continue;
        blv[tc] = calloc(lhnewn[tc] + 1, sizeof(BL));
        for (int k = 0; k < lhnewn[tc]; k++) {
            int u = lhnew[tc][k], cu = LHuc[u]; if (u == 0 || C[cu].lv != tc - 1) continue;
            int lane = laneOf[cu]; if (lane < L->nr0 || lane >= L->nr0 + L->ntr) continue;
            BL *b = &blv[tc][nbl[tc]++]; b->u = u; b->cu = cu; b->lane = lane; b->F = &L->fc[lane];
            b->ncos = 1L << (C[cu].m - C[cu].irank); b->sz = ((size_t)b->ncos * L->nbytes + 63) / 64 * 64 + 64;
            b->off = blsize[tc]; blsize[tc] += 2 * b->sz;
        }
        if (nbl[tc]) { blc[tc] = calloc((size_t)1 << LHm0, sizeof(uint8_t *)); blscr[tc] = amalloc(blsize[tc] + 128); blscr0[tc] = -1; }
        int need = 0; for (int k = 0; k < lhnewn[tc]; k++) if (lhnew[tc][k] != 0) need++;
        blfull[tc] = (unsigned char)(nbl[tc] > 0 && nbl[tc] == need && !getenv("LWE11NOTIESKIP"));
    }
}
static void bulk_rebuild(int tc, int s0, uint8_t *blk) {   // BU and tie bitmaps for every coset of cu, for this s0, into blk
    const LV *L = &LVL[tc - 1]; const int kt = L->kt;
    for (int k = 0; k < nbl[tc]; k++) {
        BL *b = &blv[tc][k]; const Con *X = &C[b->cu]; const int u = b->u;
        b->base = blk + b->off; b->tbase = blk + b->off + b->sz;
        memset(b->base, 0, (size_t)b->ncos * L->nbytes); memset(b->tbase, 0, (size_t)b->ncos * L->nbytes);
        for (long ci = 0; ci < b->ncos; ci++) {
            uint32_t crep = 0; for (int q = 0; q < X->m - X->irank; q++) if ((ci >> q) & 1) crep |= 1u << X->cbits[q];
            uint8_t *bb = b->base + ci * L->nbytes; uint32_t sv = crep;
            for (long v = 0; v < (1L << kt); v++) {
                if (v) sv ^= X->col[__builtin_ctzl(v)];
                long g = v ^ (v >> 1);
                const int ca = LHcanon[TUlo[u][sv & 255] ^ TUhi[u][sv >> 8]];
                if (ca < s0) bb[g >> 3] |= (uint8_t)(1u << (g & 7));
                if (ca == s0) b->tbase[ci * L->nbytes + (g >> 3)] |= (uint8_t)(1u << (g & 7));
            }
        }
    }
}
static void bulk_select(int tc, int s0) {     // point every lane of level tc at the bitmaps for s0 (cached, or rebuilt in scratch)
    uint8_t *blk = blc[tc][s0];
    if (!blk) {
        if (blbytes + blsize[tc] <= (size_t)BLCAP) { blk = amalloc(blsize[tc] + 128); bulk_rebuild(tc, s0, blk); blc[tc][s0] = blk; blbytes += blsize[tc]; }
        else { blk = blscr[tc]; if (blscr0[tc] != s0) { bulk_rebuild(tc, s0, blk); blscr0[tc] = s0; } }
    }
    for (int k = 0; k < nbl[tc]; k++) { BL *b = &blv[tc][k]; b->base = blk + b->off; b->tbase = blk + b->off + b->sz; }
    bls0[tc] = s0;
}
static __m512i *BACC[42];                  // rc13: per level, 2 x nz accumulators for bulk_mask
static int bulk_mask(LV *L, int t, const uint16_t *S, const u64 *w, u64 *P, u64 *T) {   // P = children rejected in bulk, T = children with a tie
    const int tc = t + 1;
    if (!nbl[tc] || probe_mode || !S) return 0;
    const int s0 = syn_ep(LHc0);
    if (bls0[tc] != s0) bulk_select(tc, s0);
    const int nz = L->nz; __m512i *acc = BACC[t], *tac = BACC[t] + nz;   // rc13: per-level accumulators, not 16 KB of stack
    for (int z = 0; z < nz; z++) acc[z] = tac[z] = _mm512_setzero_si512();
    for (int k = 0; k < nbl[tc]; k++) {
        const BL *b = &blv[tc][k]; const uint32_t s = S[b->lane];
        const uint32_t e = b->F->cvlo[s & 63] ^ b->F->cvhi[s >> 6];
        const uint32_t v0 = e & 0xFFFF; const int Z = (int)(v0 >> 9);
        const uint8_t *bp = b->base + (e >> 16), *tp = b->tbase + (e >> 16);
        const __m512i ix = OPT_IDX(v0), M = _mm512_set1_epi64((long long)AFF[v0 & 7]);
        for (int z = 0; z < nz; z++) {
            acc[z] = _mm512_or_si512(acc[z], _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix, _mm512_loadu_si512((const void *)(bp + ((size_t)(z ^ Z) << 6)))), M, 0));
            tac[z] = _mm512_or_si512(tac[z], _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix, _mm512_loadu_si512((const void *)(tp + ((size_t)(z ^ Z) << 6)))), M, 0));
        }
    }
    for (int z = 0; z < nz; z++) { u64 tmp[8] __attribute__((aligned(64))), tt[8] __attribute__((aligned(64)));
        _mm512_store_si512((void *)tmp, acc[z]); _mm512_store_si512((void *)tt, tac[z]);
        for (int q = 0; q < 8 && 8 * z + q < L->nwords; q++) { P[8 * z + q] = tmp[q] & w[8 * z + q]; T[8 * z + q] = tt[q]; } }
    return 1;
}
static void search(int t);
static void search_fast(int t);
static unsigned char fuse_lv[42];         // rc13: level whose nodes have no test: the parent calls search_fast directly
static void kids_loop_p(int t, const u64 *w, int nwords, const u64 *P, const u64 *T);
static void kids_loop(int t, const u64 *w, int nwords) { kids_loop_p(t, w, nwords, NULL, NULL); }
static u64 *PTB[42];                       // rc13: per level, P and T (nwords each, 64-byte aligned) for kids_loop_b
static void kids_loop_b(LV *L, int t, const uint16_t *S, const u64 *w) {   // kids loop with bulk LTSH for the children
    u64 *P = PTB[t], *T = PTB[t] + ((L->nwords + 7) / 8) * 8;
    if (nbl[t + 1] && bulk_mask(L, t, S, w, P, T)) kids_loop_p(t, w, L->nwords, P, blfull[t + 1] ? T : NULL); else kids_loop_p(t, w, L->nwords, NULL, NULL);
}
static void kids_loop_p(int t, const u64 *w, int nwords, const u64 *P, const u64 *T) {
    u128 clearmask = ~(((((u128)1) << (vstart[t + 1] - vstart[t])) - 1) << vstart[t]);
    if (probe_mode) {
        long cnt = 0; for (int i = 0; i < nwords; i++) cnt += __builtin_popcountll(w[i]);
        if (!cnt) return;
        long pick = (long)(rnd64() % (unsigned long long)cnt);
        for (int i = 0; i < nwords; i++) { long c = __builtin_popcountll(w[i]); if (pick < c) { u64 b = w[i]; for (long q = 0; q < pick; q++) b &= b - 1; long v = ((long)i << 6) + __builtin_ctzll(b);
                    probe_w *= (double)cnt; est[t + 1] += probe_w;
                    asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v; search(t + 1); asg &= clearmask; return; } pick -= c; }
        return;
    }
    const int fs = fsplit_ok && t + 1 == SPL, fz = fuse_lv[t + 1];
    for (int i = 0; i < nwords; i++) {
        u64 bits = w[i];
        while (bits) {
            int j = __builtin_ctzll(bits); bits &= bits - 1;
            long v = ((long)i << 6) + j;
            kids[t]++;
            if (P && ((P[i] >> j) & 1)) {      // rejected in bulk: search(t+1) would count the node and lh-prune it
                if (CHECK && !stopflag) { asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v; nid[t + 1] = ++NIDC;
                    if (!lh_reject(t + 1)) { fprintf(stderr, "CHECK bulk LTSH mismatch level %d\n", t + 1); exit(3); } }
                nodes[t + 1]++; if (!stopflag) lhprune[t + 1]++;
                continue;
            }
            if (fs && !stopflag) {             // search(t+1) would count the node, find no symmetry test and stop at the split
                nodes[t + 1]++; long long id = splitcnt++;
                if (id % NPART != PART) continue;
                presplit = 1;
            }
            asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v;
            newdone[t + 1] = (unsigned char)(T && !((T[i] >> j) & 1));
            if (fz) { nid[t + 1] = ++NIDC; SETLEV(t + 1); nodes[t + 1]++; if (!stopflag) search_fast(t + 1); }   // rc13: = search(t + 1) there
            else search(t + 1);
            newdone[t + 1] = 0; SETLEV(t);
        }
    }
    asg &= clearmask;
}
static inline int rest_lanes(LV *L, const uint16_t *S, u64 *w) {      // lanes without a translate table: child by child
    for (int i = L->nr0 + L->ntr; i < L->nc; i++) {
        const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
        for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
        if (!any) return 0;
    }
    return 1;
}
static inline __attribute__((always_inline)) int filter_zn(LV *L, const uint16_t *S, u64 *w, const int nz, const int VB) {
    // arena path for bitmaps of nz ZMMs (kt = 11, 12); returns 0 when no child survives
    const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
    const uint32_t VM = (1u << VB) - 1;
    const int nr0 = L->nr0, iend = L->nr0 + L->ntr;
    __m512i a[8];
    for (int z = 0; z < nz; z++) a[z] = _mm512_load_si512((const void *)(L->allm + 8 * z));
#define CVEZ(i) (CVL[(size_t)(i) * 64 + (S[i] & 63)] ^ CVH[(size_t)(i) * hs + (S[i] >> 6)])
    int i = nr0;
    for (; i + 1 < iend; i += 2) {
        const uint32_t e0 = CVEZ(i), e1 = CVEZ(i + 1), v0 = e0 & VM, v1 = e1 & VM;
        const uint8_t *p0 = AR + (e0 >> VB), *p1 = AR + (e1 >> VB); const int Z0 = (int)(v0 >> 9), Z1 = (int)(v1 >> 9);
        const __m512i ix0 = OPT_IDX(v0), ix1 = OPT_IDX(v1), m0 = _mm512_set1_epi64((long long)AFF[v0 & 7]), m1 = _mm512_set1_epi64((long long)AFF[v1 & 7]);
        __m512i any = _mm512_setzero_si512();
        for (int z = 0; z < nz; z++) {
            const __m512i B0 = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix0, _mm512_loadu_si512((const void *)(p0 + ((size_t)(z ^ Z0) << 6)))), m0, 0);
            const __m512i B1 = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix1, _mm512_loadu_si512((const void *)(p1 + ((size_t)(z ^ Z1) << 6)))), m1, 0);
            a[z] = _mm512_andnot_si512(_mm512_or_si512(B0, B1), a[z]); any = _mm512_or_si512(any, a[z]);
        }
        if (!_mm512_test_epi64_mask(any, any)) return 0;
    }
    for (; i < iend; i++) {
        const uint32_t e0 = CVEZ(i), v0 = e0 & VM; const uint8_t *p0 = AR + (e0 >> VB); const int Z0 = (int)(v0 >> 9);
        const __m512i ix0 = OPT_IDX(v0), m0 = _mm512_set1_epi64((long long)AFF[v0 & 7]); __m512i any = _mm512_setzero_si512();
        for (int z = 0; z < nz; z++) { a[z] = _mm512_andnot_si512(_mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix0, _mm512_loadu_si512((const void *)(p0 + ((size_t)(z ^ Z0) << 6)))), m0, 0), a[z]); any = _mm512_or_si512(any, a[z]); }
        if (!_mm512_test_epi64_mask(any, any)) return 0;
    }
#undef CVEZ
    for (int z = 0; z < nz; z++) _mm512_store_si512((void *)(w + 8 * z), a[z]);
    return 1;
}
static void search_fast_wide(LV *L, int t, const uint16_t *S) __attribute__((noinline));
static inline __attribute__((always_inline)) void search_fast_body(int t) {   // rc13: inlined in search(); search_fast = out-of-line copy
    LV *L = &LVL[t];
    fastnodes++;
    const uint16_t *S = L->vec ? s0vec(L, t) : NULL;
    const int nr0 = L->nr0, ntr = L->ntr, nc = L->nc;
    for (int i = 0; i < nr0; i++) { uint32_t s = lane_s0(L, S, i); if ((C[L->cid[i]].badbm[s >> 6] >> (s & 63)) & 1) { if (CHECK) check_node(L, t, S, NULL, 1); return; } }
#if OPT_ARENA && OPT_NARROW
    if (L->nz == 1 && L->vec && L->arena && L->kt <= 8) {   // exact-width loads and ops for bitmaps of <= 32 bytes (no line splits)
        const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
        const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const int iend = nr0 + ntr - L->ndir, dend = nr0 + ntr;
        u64 w[8] __attribute__((aligned(64))) = {0};
#define CVE(i) (CVL[(size_t)(i) * 64 + (S[i] & 63)] ^ CVH[(size_t)(i) * hs + (S[i] >> 6)])
        if (L->kt == 8) {
            __m256i al = _mm256_load_si256((const __m256i *)L->allm); const __m256i io = _mm512_castsi512_si256(IOTA);
#define TRY(i, B) do { const uint32_t e_ = CVE(i); B = _mm256_load_si256((const __m256i *)(AR + (e_ >> 9))); \
            B = _mm256_permutexvar_epi8(_mm256_xor_si256(io, _mm256_set1_epi8((char)((e_ >> 3) & 31))), B); \
            B = _mm256_gf2p8affine_epi64_epi8(B, _mm256_set1_epi64x((long long)AFF[e_ & 7]), 0); } while (0)
            int i = nr0;
            for (; i + 1 < iend; i += 2) { __m256i B0, B1; TRY(i, B0); TRY(i + 1, B1); al = _mm256_andnot_si256(_mm256_or_si256(B0, B1), al); if (_mm256_testz_si256(al, al)) goto dead; }
            for (; i < iend; i++) { __m256i B0; TRY(i, B0); al = _mm256_andnot_si256(B0, al); if (_mm256_testz_si256(al, al)) goto dead; }
            for (; i + 1 < dend; i += 2) { al = _mm256_andnot_si256(_mm256_or_si256(_mm256_load_si256((const __m256i *)(DT + DOFF[i] + (size_t)S[i] * 32)), _mm256_load_si256((const __m256i *)(DT + DOFF[i + 1] + (size_t)S[i + 1] * 32))), al); if (_mm256_testz_si256(al, al)) goto dead; }
            for (; i < dend; i++) { al = _mm256_andnot_si256(_mm256_load_si256((const __m256i *)(DT + DOFF[i] + (size_t)S[i] * 32)), al); if (_mm256_testz_si256(al, al)) goto dead; }
            _mm256_store_si256((__m256i *)w, al);
        } else if (L->kt == 7) {
            __m128i al = _mm_load_si128((const __m128i *)L->allm); const __m128i io = _mm512_castsi512_si128(IOTA);
#define TRX(i, B) do { const uint32_t e_ = CVE(i); B = _mm_load_si128((const __m128i *)(AR + (e_ >> 9))); \
            B = _mm_shuffle_epi8(B, _mm_xor_si128(io, _mm_set1_epi8((char)((e_ >> 3) & 15)))); \
            B = _mm_gf2p8affine_epi64_epi8(B, _mm_set1_epi64x((long long)AFF[e_ & 7]), 0); } while (0)
            int i = nr0;
            for (; i + 1 < iend; i += 2) { __m128i B0, B1; TRX(i, B0); TRX(i + 1, B1); al = _mm_andnot_si128(_mm_or_si128(B0, B1), al); if (_mm_testz_si128(al, al)) goto dead; }
            for (; i < iend; i++) { __m128i B0; TRX(i, B0); al = _mm_andnot_si128(B0, al); if (_mm_testz_si128(al, al)) goto dead; }
            for (; i + 1 < dend; i += 2) { al = _mm_andnot_si128(_mm_or_si128(_mm_load_si128((const __m128i *)(DT + DOFF[i] + (size_t)S[i] * 16)), _mm_load_si128((const __m128i *)(DT + DOFF[i + 1] + (size_t)S[i + 1] * 16))), al); if (_mm_testz_si128(al, al)) goto dead; }
            for (; i < dend; i++) { al = _mm_andnot_si128(_mm_load_si128((const __m128i *)(DT + DOFF[i] + (size_t)S[i] * 16)), al); if (_mm_testz_si128(al, al)) goto dead; }
            _mm_store_si128((__m128i *)w, al);
        } else {                                   // kt <= 6: one 64-bit word
            u64 al = L->allm[0]; const __m128i io = _mm512_castsi512_si128(IOTA);
#define TRQ(i, B) do { const uint32_t e_ = CVE(i); __m128i x_ = _mm_loadl_epi64((const __m128i *)(AR + (e_ >> 9))); \
            x_ = _mm_shuffle_epi8(x_, _mm_xor_si128(io, _mm_set1_epi8((char)((e_ >> 3) & 7)))); \
            B = (u64)_mm_cvtsi128_si64(_mm_gf2p8affine_epi64_epi8(x_, _mm_set1_epi64x((long long)AFF[e_ & 7]), 0)); } while (0)
            int i = nr0;
            for (; i + 1 < iend; i += 2) { u64 B0, B1; TRQ(i, B0); TRQ(i + 1, B1); al &= ~(B0 | B1); if (!al) goto dead; }
            for (; i < iend; i++) { u64 B0; TRQ(i, B0); al &= ~B0; if (!al) goto dead; }
            for (; i + 1 < dend; i += 2) { u64 b0, b1; memcpy(&b0, DT + DOFF[i] + (size_t)S[i] * 8, 8); memcpy(&b1, DT + DOFF[i + 1] + (size_t)S[i + 1] * 8, 8); al &= ~(b0 | b1); if (!al) goto dead; }
            for (; i < dend; i++) { u64 b0; memcpy(&b0, DT + DOFF[i] + (size_t)S[i] * 8, 8); al &= ~b0; if (!al) goto dead; }
            w[0] = al;
        }
        for (int i = nr0 + ntr; i < nc; i++) {           // rest: child by child
            const Con *X = &C[L->cid[i]]; uint32_t s = S[i]; int any = 0;
            for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
            if (!any) goto dead;
        }
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop_b(L, t, S, w);
        return;
    dead:
        if (CHECK) check_node(L, t, S, NULL, 1);
        return;
    }
#endif
    if (L->nz == 1) {
        __m512i al = _mm512_load_si512((const void *)L->allm);
#if OPT_ARENA
        if (L->vec && L->arena) {
            const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
#define TR1(i, B) do { uint32_t s_ = S[i]; uint32_t e_ = CVL[(size_t)(i) * 64 + (s_ & 63)] ^ CVH[(size_t)(i) * hs + (s_ >> 6)]; \
            B = _mm512_loadu_si512((const void *)(AR + (e_ >> 9))); \
            B = _mm512_permutexvar_epi8(OPT_IDX(e_), B); \
            B = _mm512_gf2p8affine_epi64_epi8(B, _mm512_set1_epi64((long long)AFF[e_ & 7]), 0); } while (0)
            int i = nr0; const int iend = nr0 + ntr - L->ndir;
#if OPT_UNROLL2
            for (; i + 1 < iend; i += 2) {
                __m512i B0, B1; TR1(i, B0); TR1(i + 1, B1);
                al = _mm512_andnot_si512(_mm512_or_si512(B0, B1), al);
                if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
            }
#endif
            for (; i < iend; i++) {
                __m512i B0; TR1(i, B0);
                al = _mm512_andnot_si512(B0, al);
                if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
            }
            if (L->ndir) {
                const uint8_t *DT = L->DT; const uint32_t *DOFF = L->DOFF; const size_t de = (size_t)L->de; const int dend = nr0 + ntr;
                for (; i + 1 < dend; i += 2) {
                    __m512i B0 = _mm512_loadu_si512((const void *)(DT + DOFF[i] + S[i] * de)), B1 = _mm512_loadu_si512((const void *)(DT + DOFF[i + 1] + S[i + 1] * de));
                    al = _mm512_andnot_si512(_mm512_or_si512(B0, B1), al);
                    if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
                }
                for (; i < dend; i++) {
                    al = _mm512_andnot_si512(_mm512_loadu_si512((const void *)(DT + DOFF[i] + S[i] * de)), al);
                    if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
                }
            }
        } else
#endif
        for (int i = nr0; i < nr0 + ntr; i++) {
            const FC *F = &L->fc[i];
            uint32_t s = lane_s0(L, S, i);
            uint32_t e = F->cvlo[s & 63] ^ F->cvhi[s >> 6];
            __m512i B = _mm512_loadu_si512((const void *)(F->base + (e >> 16)));
            B = _mm512_permutexvar_epi8(_mm512_xor_si512(IOTA, _mm512_set1_epi8((char)((e >> 3) & 63))), B);
            B = _mm512_gf2p8affine_epi64_epi8(B, _mm512_set1_epi64((long long)AFF[e & 7]), 0);
            al = _mm512_andnot_si512(B, al);
            if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        u64 w[8] __attribute__((aligned(64)));
        _mm512_store_si512((void *)w, al);
        for (int i = nr0 + ntr; i < nc; i++) {           // rest: child by child
            const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
            for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
            if (!any) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop_b(L, t, S, w);
        return;
    }
#if OPT_ARENA
    if ((L->nz == 4 || L->nz == 8) && L->vec && L->arena) {   // kt = 11, 12: four / eight ZMMs, arena layout (rc9)
        u64 w[64] __attribute__((aligned(64)));
        const int r = L->nz == 4 ? filter_zn(L, S, w, 4, 11) : filter_zn(L, S, w, 8, 12);
        if (!r || !rest_lanes(L, S, w)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop_b(L, t, S, w);
        return;
    }
    if (L->nz == 2 && L->vec && L->arena) {                 // kt = 10: two ZMMs, arena layout, test every 2 constraints
        __m512i a0 = _mm512_load_si512((const void *)L->allm), a1 = _mm512_load_si512((const void *)(L->allm + 8));
        const uint32_t *CVL = L->CVL, *CVH = L->CVH; const uint8_t *AR = L->AR; const int hs = L->hs;
#define TR2(i, B0, B1) do { uint32_t s_ = S[i]; uint32_t e_ = CVL[(size_t)(i) * 64 + (s_ & 63)] ^ CVH[(size_t)(i) * hs + (s_ >> 6)]; \
            const uint8_t *p_ = AR + (e_ >> 10); const uint32_t z_ = (e_ >> 3) & 64; \
            const __m512i ix_ = OPT_IDX(e_), m_ = _mm512_set1_epi64((long long)AFF[e_ & 7]); \
            B0 = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix_, _mm512_loadu_si512((const void *)(p_ + z_))), m_, 0); \
            B1 = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(ix_, _mm512_loadu_si512((const void *)(p_ + (z_ ^ 64)))), m_, 0); } while (0)
        int i = nr0; const int iend = nr0 + ntr;
        for (; i + 1 < iend; i += 2) {
            __m512i P0, P1, Q0, Q1; TR2(i, P0, P1); TR2(i + 1, Q0, Q1);
            a0 = _mm512_andnot_si512(_mm512_or_si512(P0, Q0), a0); a1 = _mm512_andnot_si512(_mm512_or_si512(P1, Q1), a1);
            if (!_mm512_test_epi64_mask(_mm512_or_si512(a0, a1), _mm512_or_si512(a0, a1))) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        for (; i < iend; i++) {
            __m512i P0, P1; TR2(i, P0, P1);
            a0 = _mm512_andnot_si512(P0, a0); a1 = _mm512_andnot_si512(P1, a1);
            if (!_mm512_test_epi64_mask(_mm512_or_si512(a0, a1), _mm512_or_si512(a0, a1))) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        u64 w[16] __attribute__((aligned(64)));
        _mm512_store_si512((void *)w, a0); _mm512_store_si512((void *)(w + 8), a1);
        for (int k2 = nr0 + ntr; k2 < nc; k2++) {           // rest: child by child
            const Con *X = &C[L->cid[k2]]; uint32_t sr = lane_s0(L, S, k2); int any = 0;
            for (int k = 0; k < 16; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, sr, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
            if (!any) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop_b(L, t, S, w);
        return;
    }
#endif
    search_fast_wide(L, t, S);
}
static void search_fast_wide(LV *L, int t, const uint16_t *S) {   // rc13: the wide paths, outside search_fast's frame
    const int nr0 = L->nr0, ntr = L->ntr, nc = L->nc;
    // multi-ZMM bitmaps (kt >= 10), list mode below L->thr survivors
    const int nz = L->nz;
    __m512i A[128];
    for (int z = 0; z < nz; z++) A[z] = _mm512_load_si512((const void *)(L->allm + 8 * z));
    int i = nr0;
    uint32_t list[64]; int nlist = -1;
    for (; i < nr0 + ntr; i++) {
        const FC *F = &L->fc[i];
        uint32_t s = lane_s0(L, S, i);
        uint32_t e = F->cvlo[s & 63] ^ F->cvhi[s >> 6];
        const uint8_t *bp = F->base + (e >> 16);
        const __m512i idx = _mm512_xor_si512(IOTA, _mm512_set1_epi8((char)((e >> 3) & 63)));
        const __m512i M = _mm512_set1_epi64((long long)AFF[e & 7]);
        const int Z = (int)((e & 0xFFFF) >> 9);
        __m512i any = _mm512_setzero_si512();
        for (int z = 0; z < nz; z++) {
            __m512i B = _mm512_loadu_si512((const void *)(bp + ((size_t)(z ^ Z) << 6)));
            B = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(idx, B), M, 0);
            A[z] = _mm512_andnot_si512(B, A[z]);
            any = _mm512_or_si512(any, A[z]);
        }
        if (!_mm512_test_epi64_mask(any, any)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        if (L->thr > 0) {
            long cnt = 0; for (int z = 0; z < nz; z++) cnt += _mm512_reduce_add_epi64(_mm512_popcnt_epi64(A[z]));
            if (cnt <= L->thr) {
                u64 w[8] __attribute__((aligned(64))); nlist = 0;
                for (int z = 0; z < nz; z++) { _mm512_store_si512((void *)w, A[z]); for (int k = 0; k < 8; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; list[nlist++] = (uint32_t)((z << 9) + (k << 6) + j); } } }
                i++; break;
            }
        }
    }
    if (nlist >= 0) {
        for (; i < nr0 + ntr; i++) {
            const FC *F = &L->fc[i]; const u64 *bb = C[L->cid[i]].badbm;
            uint32_t s = lane_s0(L, S, i); int nl = 0;
            for (int q = 0; q < nlist; q++) {
                uint32_t x = list[q]; uint32_t sv = s ^ F->vlo[x & 255] ^ F->vhi[x >> 8];
                int bad = (int)((bb[sv >> 6] >> (sv & 63)) & 1);
                list[nl] = x; nl += 1 - bad;
            }
            nlist = nl; if (!nlist) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        for (; i < nc; i++) {
            const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int nl = 0;
            for (int q = 0; q < nlist; q++) { uint32_t x = list[q]; int bad = bad_child(X, s, x); list[nl] = x; nl += 1 - bad; }
            nlist = nl; if (!nlist) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        u64 w[128 * 8] __attribute__((aligned(64)));
        memset(w, 0, sizeof(u64) * L->nwords);
        for (int q = 0; q < nlist; q++) w[list[q] >> 6] |= 1ULL << (list[q] & 63);   // list is in increasing order
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop_b(L, t, S, w);
        return;
    }
    u64 w[128 * 8] __attribute__((aligned(64)));
    for (int z = 0; z < nz; z++) _mm512_store_si512((void *)(w + 8 * z), A[z]);
    for (; i < nc; i++) {
        const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
        for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
        if (!any) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
    }
    if (CHECK) check_node(L, t, S, w, 0);
    kids_loop_b(L, t, S, w);
}
static void search_fast(int t) { search_fast_body(t); }
static void search(int t) {
    nid[t] = ++NIDC; SETLEV(t);
    if (t == NLEV) {
        if (SYM && sym_reject(t)) { symprune[t]++; return; }
        if (LR && ltsr_reject(t)) { ltsprune[t]++; return; }
        if (LH && (LH2 ? lh_reject2(t) : lh_reject(t))) { lhprune[t]++; return; }
        nsol++;
        printf("SOLUTION %016llx%016llx\n", (unsigned long long)(asg >> 64), (unsigned long long)asg); fflush(stdout);
        return;
    }
    if (presplit) {                       // counted and split-checked by the parent (fast split)
        presplit = 0;
        if (stopflag) return;
        if (CHECK && LH && lh_reject(t)) { fprintf(stderr, "CHECK fast split at level %d\n", t); exit(3); }
        if (CHECK && LB && lb_reject_full(t)) { fprintf(stderr, "CHECK fast split (LB) at level %d\n", t); exit(3); }
        goto past_split;
    }
    nodes[t]++;
    if (stopflag) return;
    if (SYM && sym_reject(t)) { symprune[t]++; return; }
    if (LR && ltsr_reject(t)) { ltsprune[t]++; return; }
    if (CHECK && LH && LH2) {          // every node: lh_reject2 (and the skip at inactive levels) must agree with lh_reject
        const int r2 = lhact[t] ? lh_reject2(t) : 0, r1 = lh_reject(t);
        if (r1 != r2) { fprintf(stderr, "CHECK lh_reject2 %d != lh_reject %d at level %d\n", r2, r1, t); exit(3); }
        if (r2) { lhprune[t]++; return; }
    } else
    if (LH && lhact[t] && (LH2 ? lh_reject2(t) : lh_reject(t))) { lhprune[t]++; return; }
    if (LB) {                          // rc11: bit-granular comparands after the LTSH test (as lwe10b's lh_reject)
        const int rb = lbact[t] ? lb_reject_fast(t) : 0;
        if (CHECK) { const int rf = lb_reject_full(t); lbchecked++;
            if (rf != rb) { fprintf(stderr, "CHECK lb fast %d != full %d at level %d\n", rb, rf, t); exit(3); } }
        if (rb) { lbprune[t]++; lhprune[t]++; return; }
    }
    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }
past_split:
    if (LVL[t].on) { search_fast_body(t); return; }
    int kt = vstart[t + 1] - vstart[t];
    long nch = 1L << kt; int nw = (int)((nch + 63) / 64);
    u64 *A = alive[t];
    for (int i = 0; i < nw; i++) A[i] = ~0ULL;
    if (nch % 64) A[nw - 1] = (1ULL << (nch % 64)) - 1;
    int listmode = 0; int nlist = 0; uint32_t list[64];
    for (int ci = lstart[t]; ci < lstart[t + 1]; ci++) {
        Con *X = &C[ORD[ci]];
        int s0 = syn0(X);
        if (listmode) {
            if (X->method == 2) { if ((X->badbm[s0 >> 6] >> (s0 & 63)) & 1) return; continue; }
            int nl = 0;
            if (X->V) {
                const uint16_t *V = X->V; const u64 *bb = X->badbm;
                for (int q = 0; q < nlist; q++) {      // branch-free compaction
                    uint32_t x = list[q]; int sv = s0 ^ V[x];
                    int bad = (int)((bb[sv >> 6] >> (sv & 63)) & 1);
                    list[nl] = x; nl += 1 - bad;
                }
            } else
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
            for (int q = 0; q < X->irank; q++) { uint32_t mk = 0u - ((sv >> X->ipiv[q]) & 1u); sv ^= X->ivec[q] & mk; v0 ^= X->ipre[q] & mk; }
            long ci2 = 0;
            for (int q = 0; (1L << q) < X->ncos; q++) if ((sv >> X->cbits[q]) & 1) ci2 |= 1L << q;
            u64 *tmp = tmpbuf;
            const u64 *Bm = X->base + ci2 * nw;
            if (nch < 64) { u64 w = Bm[0]; u64 o = w; uint32_t d = v0; o = w;
                for (int j = 0; j < 6; j++) { int sh = 1 << j; u64 M = TMASK[j]; u64 mk = 0ULL - (u64)((d >> j) & 1); u64 sw = ((o & M) << sh) | ((o >> sh) & M); o = (o & ~mk) | (sw & mk); }
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
    kids_loop(t, A, nw);
}

// The engine below is compiled for AVX-512; this entry point is compiled for baseline x86-64, so that on CPUs without
// the needed extensions the program stops with a message before any AVX-512 instruction runs (rc7).
static int lwe11_main(int argc, char **argv) __attribute__((noinline));
__attribute__((target("arch=x86-64"))) int main(int argc, char **argv) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx512f") || !__builtin_cpu_supports("avx512bw") || !__builtin_cpu_supports("avx512vl") ||
        !__builtin_cpu_supports("avx512vbmi") || !__builtin_cpu_supports("avx512vpopcntdq") || !__builtin_cpu_supports("gfni")) {
        fputs("lwe11: this CPU lacks AVX-512 F/BW/VL/VBMI/VPOPCNTDQ or GFNI (needs <CPU>/5 or <CPU>+); run lwe10 here instead.\n", stderr);
        return 2;
    }
    return lwe11_main(argc, argv);
}
static int lwe11_main(int argc, char **argv) {
    if (argc < 2) die("usage: lwe INSTANCE [SPLITLEVEL NPART PART]");
    read_inst(argv[1]);
    make_order();
    build_tables();
    for (int l = 0; l < 42; l++) nid[l] = ++NIDC;
    { const char *sf = getenv("SYMFILE"); if (sf) read_sym(sf); }
    { const char *lf = getenv("LTSFILE"); if (lf) read_ltsr(lf); }
    { const char *hf = getenv("LTSHFILE"); if (hf) read_ltsh(hf); }
    { const char *bf = getenv("LTSBFILE"); if (bf) { read_ltsb(bf); build_lb(); } }
    CHECK = getenv("LWE11CHECK") != NULL;
    if (!__builtin_cpu_supports("avx512vbmi") || !__builtin_cpu_supports("gfni") || !__builtin_cpu_supports("avx512bw") || !__builtin_cpu_supports("avx512vpopcntdq")) die("lwe11 needs AVX-512 VBMI, BW, VPOPCNTDQ and GFNI");
    build_fast();
    if (LH) build_lh2();
    if (LH) build_bulk();
    LH2 = getenv("LWE11OLDLH") == NULL;
    if (argc > 4) { SPL = atoi(argv[2]); NPART = atoi(argv[3]); PART = atoi(argv[4]); }
    fsplit_ok = SPL > 0 && SPL < NLEV && !SYM && !LR && !(LH && lhact[SPL]) && !(LB && lbact[SPL]) && !getenv("LWE11NOFASTSPLIT");
    for (int l = 1; l < NLEV; l++)          // rc13: child fusion where search() would run no test before search_fast
        fuse_lv[l] = (unsigned char)(!CHECK && !SYM && !LR && !(LH && lhact[l]) && !(LB && lbact[l]) && l != SPL && LVL[l].on && !getenv("LWE11NOFUSE"));
    int kmax = 0; for (int t = 0; t < NLEV; t++) { int k = vstart[t + 1] - vstart[t]; if (k > kmax) kmax = k; }
    for (int t = 0; t < NLEV; t++) alive[t] = malloc(sizeof(u64) * (((1L << kmax) + 63) / 64 + 1));
    for (int t = 0; t < NLEV; t++) {        // rc13: bulk mask buffers per level
        const int k = vstart[t + 1] - vstart[t]; const long nw = k >= 6 ? 1L << (k - 6) : 1, nw8 = (nw + 7) / 8 * 8;
        PTB[t] = aligned_alloc(64, sizeof(u64) * (size_t)(2 * nw8 + 16)); if (!PTB[t]) die("alloc"); memset(PTB[t], 0, sizeof(u64) * (size_t)(2 * nw8 + 16));
        const long nz = nw8 / 8 > 0 ? nw8 / 8 : 1; BACC[t] = aligned_alloc(64, sizeof(__m512i) * (size_t)(2 * nz + 2)); if (!BACC[t]) die("alloc");
    }
    tmpbuf = malloc(sizeof(u64) * (((1L << kmax) + 63) / 64 + 1));
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
#ifdef PROFPC
    if (getenv("PROFOUT")) prof_start();
#endif
    search(0);
#ifdef PROFPC
    if (getenv("PROFOUT")) prof_dump();
#endif
    if (stopflag) printf("STOPPED (partial counts)\n");
    printf("DONE lwe nsol %lld time %lds split %d part %d/%d N %d\n", nsol, (long)(time(NULL) - t0), SPL, PART, NPART, N);
    for (int t = 0; t < NLEV; t++) printf("LEVEL %d kt %d ncons %d nodes %lld kids %lld symprune %lld ltsprune %lld lhprune %lld\n", t, vstart[t + 1] - vstart[t], lstart[t + 1] - lstart[t], nodes[t], kids[t], symprune[t], ltsprune[t], lhprune[t]);
    printf("SYMPRUNE at leaves %lld LTSPRUNE at leaves %lld LHPRUNE at leaves %lld\n", symprune[NLEV], ltsprune[NLEV], lhprune[NLEV]);
    if (LB) { printf("LBPRUNE"); for (int t = 0; t <= NLEV; t++) printf(" %d:%lld", t, lbprune[t]); printf("\n"); }
    if (CHECK && LB) fprintf(stderr, "LB check: %lld nodes compared with the full test\n", lbchecked);
    if (CHECK) fprintf(stderr, "LWE11CHECK passed: %lld fast nodes checked\n", checknodes);
    return 0;
}
