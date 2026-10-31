/* Thin wrapper (separate translation unit) around c3class's cform.h (read-only copy in c3c/) so that rglue.c can
   compute c3class's class key without mixing the two F4 libraries.  Same bit layout on both sides: coordinate i
   holds a_i + b_i w with a = lo plane, b = hi plane.
   Build: gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -Ic3c -Inauty -c ckey.c */
#include "c3c/cform.h"
/* key under Mon x conj (k rows, length n, minimum weight d used for the word set), |Aut_Mon|, self-conjugate flag.
   Returns 0 on success. */
int c3c_class_key(const unsigned *lo, const unsigned *hi, int k, int n, int d, unsigned *klo, unsigned *khi,
                  double *aut, int *sc) {
    f4v gen[16], key[16];
    for (int r = 0; r < k; r++) { gen[r].a = lo[r]; gen[r].b = hi[r]; }
    if (canon_class(gen, k, n, d, key, aut, sc)) return -1;
    for (int r = 0; r < k; r++) { klo[r] = key[r].a; khi[r] = key[r].b; }
    return 0;
}
/* Same key, but with the word set supplied by the caller (must be exactly the set cform's canon_code would use:
   all words of weight in [d, w] for the smallest spanning w; for d(C) = d with weight-d words spanning this is the
   set of all weight-d words).  Mirrors canon_class: canon_from_words on C and on conj C (conjugated word set),
   key = smaller, aut from C, selfconj = equal.  Avoids canon_code's word enumeration. */
int c3c_class_key_wl(const unsigned *lo, const unsigned *hi, int k, int n, const unsigned *wlo, const unsigned *whi,
                     long nw, unsigned *klo, unsigned *khi, double *aut, int *sc) {
    f4v gen[16], g2[16], c1[16], c2[16]; double a1, a2;
    f4v *W1 = malloc(sizeof(f4v) * (nw + 1)), *W2 = malloc(sizeof(f4v) * (nw + 1));
    for (long j = 0; j < nw; j++) { W1[j].a = wlo[j]; W1[j].b = whi[j]; W2[j] = f4conj(W1[j]); }
    for (int r = 0; r < k; r++) { gen[r].a = lo[r]; gen[r].b = hi[r]; g2[r] = f4conj(gen[r]); }
    int e1 = canon_from_words(gen, k, n, W1, (int)nw, c1, &a1), e2 = canon_from_words(g2, k, n, W2, (int)nw, c2, &a2);
    free(W1); free(W2);
    if (e1 || e2) return -1;
    int c = mat_cmp(c1, c2, k);
    const f4v *key = c <= 0 ? c1 : c2;
    for (int r = 0; r < k; r++) { klo[r] = key[r].a; khi[r] = key[r].b; }
    *aut = a1; *sc = (c == 0);
    return 0;
}
