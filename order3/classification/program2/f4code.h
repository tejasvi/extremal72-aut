/* F4 codes of length <= 32, bit-sliced: element a + b w as bits (lo, hi); w^2 = w + 1. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
typedef uint32_t u32;
typedef uint64_t u64;
typedef struct { u32 lo, hi; } vec;
static inline vec vadd(vec a, vec b) { vec r = { a.lo ^ b.lo, a.hi ^ b.hi }; return r; }
static inline vec vmulw(vec a) { vec r = { a.hi, a.lo ^ a.hi }; return r; }
static inline vec vscal(int lam, vec a) { if (!lam) { vec z = {0,0}; return z; } if (lam == 1) return a; if (lam == 2) return vmulw(a); return vmulw(vmulw(a)); }
static inline u32 vsupp(vec a) { return a.lo | a.hi; }
static inline int vwt(vec a) { return __builtin_popcount(a.lo | a.hi); }
static inline int vget(vec a, int i) { return ((a.lo >> i) & 1) | (((a.hi >> i) & 1) << 1); }
static inline void vset(vec *a, int i, int c) { a->lo = (a->lo & ~(1u << i)) | ((u32)(c & 1) << i); a->hi = (a->hi & ~(1u << i)) | ((u32)((c >> 1) & 1) << i); }
/* Hermitian product sum u_i conj(v_i); conj(x0 + x1 w) = (x0^x1) + x1 w */
static inline int vherm(vec u, vec v) {
    u32 cl = v.lo ^ v.hi, ch = v.hi;
    u32 p0 = (u.lo & cl) ^ (u.hi & ch), p1 = (u.lo & ch) ^ (u.hi & cl) ^ (u.hi & ch);
    return (__builtin_popcount(p0) & 1) | ((__builtin_popcount(p1) & 1) << 1);
}
static const int f4mul[4][4] = { {0,0,0,0}, {0,1,2,3}, {0,2,3,1}, {0,3,1,2} };
static const int f4inv[4] = { 0, 1, 3, 2 };
static const int f4conj[4] = { 0, 1, 3, 2 };
/* rng */
static u64 rs_state = 0x9E3779B97F4A7C15ULL;
static inline void rnd_seed(u64 seed) { u64 z = seed + 0x9E3779B97F4A7C15ULL; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; rs_state = (z ^ (z >> 31)) | 1; }
static inline u64 rnd64(void) { u64 x = rs_state; x ^= x << 13; x ^= x >> 7; x ^= x << 17; rs_state = x; return x; }
/* row reduce k vectors (in place), returns rank; basis in reduced echelon form; piv[] pivots */
static int vrref(vec *g, int k, int n, int *piv) {
    int r = 0;
    for (int col = 0; col < n && r < k; col++) {
        int sel = -1;
        for (int i = r; i < k; i++) if (vget(g[i], col)) { sel = i; break; }
        if (sel < 0) continue;
        vec t = g[sel]; g[sel] = g[r]; g[r] = t;
        g[r] = vscal(f4inv[vget(g[r], col)], g[r]);
        for (int i = 0; i < k; i++) if (i != r) { int c = vget(g[i], col); if (c) g[i] = vadd(g[i], vscal(c, g[r])); }
        piv[r++] = col;
    }
    return r;
}
/* all 4^h combinations of h generators into out[] (out size 4^h) */
static void combos(const vec *g, int h, vec *out) {
    out[0].lo = out[0].hi = 0; int sz = 1;
    for (int j = 0; j < h; j++) {
        vec g1 = g[j], g2 = vmulw(g1), g3 = vmulw(g2);
        for (int t = 0; t < sz; t++) { out[sz + t] = vadd(out[t], g1); out[2 * sz + t] = vadd(out[t], g2); out[3 * sz + t] = vadd(out[t], g3); }
        sz *= 4;
    }
}
