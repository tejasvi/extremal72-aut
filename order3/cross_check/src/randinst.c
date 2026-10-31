/* randinst.c -- random forbidden families (no code structure) with one planted labelled Golay code.
   usage: randinst DENS8 DENS12 SEED OUTPREFIX  -> OUTPREFIX.f8/.f12 raw bitmaps; prints planted hash */
#include "golay24.h"
static uint64_t rs;
static uint64_t rnd(void) { rs += 0x9e3779b97f4a7c15ULL; uint64_t z = rs; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
static double ur(void) { return (double)(rnd() >> 11) * 0x1.0p-53; }
static uint64_t code_hash_c3(const uint32_t *B) {
    uint32_t R[12]; memcpy(R, B, sizeof R); int r = 0;
    for (int c = 23; c >= 0 && r < 12; c--) {
        int p = -1; for (int i = r; i < 12; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        uint32_t t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < 12; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < 12; i++) { h ^= R[i]; h *= 1099511628211ULL; h ^= h >> 29; }
    return h;
}
int main(int argc, char **argv) {
    double d8 = atof(argv[1]), d12 = atof(argv[2]); rs = strtoull(argv[3], 0, 10) * 31337 + 5;
    golay_build();
    uint8_t *F8 = calloc(1u << 21, 1), *F12 = calloc(1u << 21, 1);
    for (uint32_t s = 0; s < (1u << 24); s++) {
        int c = __builtin_popcount(s);
        if (c == 8 && ur() < d8) F8[s >> 3] |= (uint8_t)(1u << (s & 7));
        if (c == 12 && ur() < d12) F12[s >> 3] |= (uint8_t)(1u << (s & 7));
    }
    int pm[24]; for (int i = 0; i < 24; i++) pm[i] = i;
    for (int i = 23; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
    for (int k = 0; k < 759; k++) { uint32_t o = perm_apply(pm, OCT[k]); F8[o >> 3] &= (uint8_t)~(1u << (o & 7)); }
    for (int k = 0; k < 2576; k++) { uint32_t o = perm_apply(pm, DOD[k]); F12[o >> 3] &= (uint8_t)~(1u << (o & 7)); }
    uint32_t B[12]; for (int i = 0; i < 12; i++) B[i] = perm_apply(pm, GB[i]);
    char fn[4096];
    snprintf(fn, sizeof fn, "%s.f8", argv[4]); FILE *f = fopen(fn, "wb"); fwrite(F8, 1, 1u << 21, f); fclose(f);
    snprintf(fn, sizeof fn, "%s.f12", argv[4]); f = fopen(fn, "wb"); fwrite(F12, 1, 1u << 21, f); fclose(f);
    printf("%s planted_hash=%016llx\n", argv[4], (unsigned long long)code_hash_c3(B));
    return 0;
}
