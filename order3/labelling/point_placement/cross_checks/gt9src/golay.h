/* The extended binary Golay code G24 as 24-bit masks: generator from the cyclic [23,12,7] QR code
   (g(x) = 1 + x^2 + x^4 + x^5 + x^6 + x^10 + x^11) plus an overall parity bit (bit 23). */
#ifndef GOLAY_H
#define GOLAY_H
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#define FULL24 0xFFFFFFu
static void golay_gen(uint32_t *gen) {
    uint32_t g = (1u << 0) | (1u << 2) | (1u << 4) | (1u << 5) | (1u << 6) | (1u << 10) | (1u << 11);
    for (int s = 0; s < 12; s++) {
        uint32_t r = g << s;                       /* degree <= 22, fits in 23 bits */
        if (__builtin_popcount(r) & 1) r |= 1u << 23;
        gen[s] = r;
    }
}
/* all 4096 codewords; returns counts check */
static void golay_words(uint32_t *W) {
    uint32_t gen[12]; golay_gen(gen);
    for (int m = 0; m < 4096; m++) {
        uint32_t w = 0;
        for (int i = 0; i < 12; i++) if ((m >> i) & 1) w ^= gen[i];
        W[m] = w;
    }
    int cnt[25] = { 0 };
    for (int m = 0; m < 4096; m++) cnt[__builtin_popcount(W[m])]++;
    if (cnt[0] != 1 || cnt[8] != 759 || cnt[12] != 2576 || cnt[16] != 759 || cnt[24] != 1) {
        fprintf(stderr, "golay_words: bad weight distribution\n"); exit(1);
    }
}
#endif
