/* Independent check of set_forbidden_from_E (gcore.h): supports of weight 8/10/12 by FULL Gray-code enumeration of
   all 4^12 codewords (no information sets), then F8/F12 recomputed by direct membership tests over all 8-/12-sets. */
#include "gcore.h"
static uint8_t *b8, *b10, *b12;   /* bitmaps over 2^24 masks */
#define GB(bm,m) (((bm)[(m)>>3]>>((m)&7))&1)
#define SB(bm,m) ((bm)[(m)>>3] |= (uint8_t)(1u<<((m)&7)))
int main(int argc, char **argv) {
    gcore_init();
    b8 = calloc(1<<21,1); b10 = calloc(1<<21,1); b12 = calloc(1<<21,1);
    FILE *f = fopen(argv[1], "r"); long maxc = argc > 2 ? atol(argv[2]) : 1000000; char line[8192]; long ln = 0, totbad = 0;
    while (ln < maxc && fgets(line, sizeof line, f)) {
        f4v gen[12]; if (!parse_code_line(line, gen)) { printf("line %ld unparsable\n", ln); ln++; continue; }
        memset(b8,0,1<<21); memset(b10,0,1<<21); memset(b12,0,1<<21);
        f4v B[24]; for (int i = 0; i < 12; i++) { B[2*i] = gen[i]; B[2*i+1] = f4mw(gen[i]); }
        f4v cur = {0,0}; long A[25] = {0}; long n8=0,n10=0,n12=0;
        for (uint32_t g = 1; g < (1u<<24); g++) {
            cur = f4add(cur, B[__builtin_ctz(g)]);
            uint32_t s = f4supp(cur); int w = __builtin_popcount(s); A[w]++;
            if (w == 8 && !GB(b8,s)) { SB(b8,s); n8++; }
            if (w == 10 && !GB(b10,s)) { SB(b10,s); n10++; }
            if (w == 12 && !GB(b12,s)) { SB(b12,s); n12++; }
        }
        set_forbidden_from_E(gen);
        long bad8 = 0, bad12 = 0, nf8 = 0, nf12 = 0;
        for (uint32_t m = 0; m < (1u<<24); m++) {
            int c = __builtin_popcount(m);
            if (c == 8) {
                int fb = GB(b8, m);
                for (uint32_t a = m; a && !fb; a &= a-1) for (uint32_t b = FULL24 & ~m; b && !fb; b &= b-1) if (GB(b8, (m ^ (a&-a)) | (b&-b))) fb = 1;
                for (uint32_t a = FULL24 & ~m; a && !fb; a &= a-1) for (uint32_t b = a & (a-1); b && !fb; b &= b-1) if (GB(b10, m | (a&-a) | (b&-b))) fb = 1;
                nf8 += fb; if (fb != F8(m)) bad8++;
            } else if (c == 12) {
                int fb = GB(b12, m); nf12 += fb; if (fb != F12(m)) bad12++;
            }
        }
        int wd_ok = (A[0]==0 && A[2]==0 && A[4]==0 && A[6]==0 && A[1]+A[3]+A[5]+A[7]==0);
        printf("line %ld: A8=%ld A10=%ld A12=%ld supports %ld/%ld/%ld vs E_n %d/%d/%d forb8=%ld forb12=%ld bad8=%ld bad12=%ld wdlow_ok=%d\n",
               ln, A[8], A[10], A[12], n8, n10, n12, E_n8, E_n10, E_n12, nf8, nf12, bad8, bad12, wd_ok);
        if (bad8 || bad12 || n8 != E_n8 || n10 != E_n10 || n12 != E_n12 || !wd_ok) totbad++;
        fflush(stdout); ln++;
    }
    printf("codes %ld, mismatching %ld\n", ln, totbad);
    return 0;
}
