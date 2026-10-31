#include "golay.h"
#include <stdio.h>
int main(void) { uint32_t g[12]; golay_gen(g); for (int i = 0; i < 12; i++) printf("%08x%08x", g[i], 0u); printf("\n"); return 0; }
