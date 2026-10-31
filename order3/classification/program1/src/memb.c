/* membership check: class keys of sampled codes (rsd format) must be in the classification (keys file: first
   field = 192-hex canonical generator, sorted unique).  Usage: memb keysfile samplefile [max] */
#include "cform.h"
typedef struct { uint32_t w[24]; } ckey_t;
static ckey_t *keys; static long nkeys;
static int kcmp(const void *a, const void *b) { return memcmp(a, b, sizeof(ckey_t)); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[1024]; long cap = 1 << 20;
    keys = malloc(sizeof(ckey_t) * cap);
    while (fgets(line, sizeof line, f)) {
        if (nkeys == cap) { cap *= 2; keys = realloc(keys, sizeof(ckey_t) * cap); }
        for (int r = 0; r < 12; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; keys[nkeys].w[2 * r] = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); keys[nkeys].w[2 * r + 1] = strtoul(t, 0, 16); }
        nkeys++;
    }
    fclose(f);
    qsort(keys, nkeys, sizeof(ckey_t), kcmp);
    fprintf(stderr, "%ld keys loaded\n", nkeys);
    f = fopen(argv[2], "r"); long maxs = argc > 3 ? atol(argv[3]) : 1L << 40, tested = 0, miss = 0;
    while (tested < maxs && fgets(line, sizeof line, f)) {
        f4v gen[12]; for (int r = 0; r < 12; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; gen[r].a = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); gen[r].b = strtoul(t, 0, 16); }
        f4v kk[12]; double a; int sc;
        canon_class(gen, 12, 24, 8, kk, &a, &sc);
        ckey_t K; for (int r = 0; r < 12; r++) { K.w[2 * r] = kk[r].a; K.w[2 * r + 1] = kk[r].b; }
        tested++;
        if (!bsearch(&K, keys, nkeys, sizeof(ckey_t), kcmp)) { miss++; if (miss <= 5) printf("MISSING sample %ld: %s", tested - 1, line); }
    }
    printf("samples tested %ld, missing %ld\n", tested, miss);
    return 0;
}
