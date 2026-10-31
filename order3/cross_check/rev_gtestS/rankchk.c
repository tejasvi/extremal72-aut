/* F2-rank of the weight-8 words (as 48-bit vectors a|b<<24; the set is closed under F4 scalars, so F2-rank = 2*F4-rank) */
#include "f4code.h"
static uint64_t piv[64]; static int rk;
static void addvec(uint64_t v) { for (int b = 47; b >= 0 && v; b--) if ((v >> b) & 1) { if (piv[b]) v ^= piv[b]; else { piv[b] = v; rk++; return; } } }
static long n8;
static void cb(f4v w, int nr, void *c) { if (f4wt(w) != 8) return; n8++; addvec((uint64_t)w.a | ((uint64_t)w.b << 24)); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[8192]; long ln = 0, def = 0;
    while (fgets(line, sizeof line, f)) {
        f4v gen[12];
        for (int i = 0; i < 12; i++) { char t[9]; memcpy(t, line + 16 * i, 8); t[8] = 0; gen[i].a = strtoul(t, 0, 16); memcpy(t, line + 16 * i + 8, 8); gen[i].b = strtoul(t, 0, 16); }
        memset(piv, 0, sizeof piv); rk = 0; n8 = 0;
        sd_lowwords(gen, 24, 8, cb, NULL);
        if (rk != 24) { def++; printf("deficient line %ld F2rank %d A8 %ld | %s", ln, rk, n8, line + 193); }
        ln++;
    }
    printf("lines %ld deficient %ld\n", ln, def);
    return 0;
}
