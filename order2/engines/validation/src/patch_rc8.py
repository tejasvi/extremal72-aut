# Patch: (1) bulk LTSH tables cached per s0 value (cap BLCAP bytes, scratch rebuild beyond); (2) fast split skip at
# the parent of the split level.  Applies to lwe11 rc7 (-> rc8) and lwe11b (-> lwe11b2).
import sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old[:80], s.count(old))
    s = s.replace(old, new)
# --- (1) cache ---
rep('typedef struct { int u, cu, lane; const FC *F; uint8_t *base, *tbase; long ncos; } BL;\nstatic BL *blv[42]; static int nbl[42]; static int bls0[42];',
    'typedef struct { int u, cu, lane; const FC *F; uint8_t *base, *tbase; long ncos; size_t off, sz; } BL;\n'
    'static BL *blv[42]; static int nbl[42]; static int bls0[42];\n'
    '// rc8: the BU bitmaps of all lanes of a level are one block per s0 value, cached (s0 is fixed below the key\'s level, so\n'
    '// with a deep key word it changes at every node of level lv0+1); beyond BLCAP bytes a scratch block is rebuilt.\n'
    '#ifndef BLCAP\n#define BLCAP (48L << 20)\n#endif\n'
    'static uint8_t **blc[42], *blscr[42]; static size_t blsize[42], blbytes = 0; static int blscr0[42];')
rep('''            b->ncos = 1L << (C[cu].m - C[cu].irank); b->base = amalloc((size_t)b->ncos * L->nbytes + 128);
            b->tbase = amalloc((size_t)b->ncos * L->nbytes + 128);
        }''',
'''            b->ncos = 1L << (C[cu].m - C[cu].irank); b->sz = ((size_t)b->ncos * L->nbytes + 63) / 64 * 64 + 64;
            b->off = blsize[tc]; blsize[tc] += 2 * b->sz;
        }
        if (nbl[tc]) { blc[tc] = calloc((size_t)1 << LHm0, sizeof(uint8_t *)); blscr[tc] = amalloc(blsize[tc] + 128); blscr0[tc] = -1; }''')
rep('''static void bulk_rebuild(int tc, int s0) {   // base bitmaps of BU for every coset of cu, for this s0
    const LV *L = &LVL[tc - 1]; const int kt = L->kt;
    for (int k = 0; k < nbl[tc]; k++) {
        BL *b = &blv[tc][k]; const Con *X = &C[b->cu]; const int u = b->u;''',
'''static void bulk_rebuild(int tc, int s0, uint8_t *blk) {   // BU and tie bitmaps for every coset of cu, for this s0, into blk
    const LV *L = &LVL[tc - 1]; const int kt = L->kt;
    for (int k = 0; k < nbl[tc]; k++) {
        BL *b = &blv[tc][k]; const Con *X = &C[b->cu]; const int u = b->u;
        b->base = blk + b->off; b->tbase = blk + b->off + b->sz;''')
rep('''    bls0[tc] = s0;
}''', '''}
static void bulk_select(int tc, int s0) {     // point every lane of level tc at the bitmaps for s0 (cached, or rebuilt in scratch)
    uint8_t *blk = blc[tc][s0];
    if (!blk) {
        if (blbytes + blsize[tc] <= (size_t)BLCAP) { blk = amalloc(blsize[tc] + 128); bulk_rebuild(tc, s0, blk); blc[tc][s0] = blk; blbytes += blsize[tc]; }
        else { blk = blscr[tc]; if (blscr0[tc] != s0) { bulk_rebuild(tc, s0, blk); blscr0[tc] = s0; } }
    }
    for (int k = 0; k < nbl[tc]; k++) { BL *b = &blv[tc][k]; b->base = blk + b->off; b->tbase = blk + b->off + b->sz; }
    bls0[tc] = s0;
}''')
rep('    if (bls0[tc] != s0) bulk_rebuild(tc, s0);', '    if (bls0[tc] != s0) bulk_select(tc, s0);')
# --- (2) fast split ---
rep('static unsigned char newdone[42];', 'static unsigned char newdone[42];\nstatic int fsplit_ok = 0, presplit = 0;   // rc8: the split level\'s parent counts split-rejected children itself')
rep('''            asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v;
            newdone[t + 1] = (unsigned char)(T && !((T[i] >> j) & 1));''',
'''            if (fs && !stopflag) {             // search(t+1) would count the node, find no symmetry test and stop at the split
                nodes[t + 1]++; long long id = splitcnt++;
                if (id % NPART != PART) continue;
                presplit = 1;
            }
            asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v;
            newdone[t + 1] = (unsigned char)(T && !((T[i] >> j) & 1));''')
rep('    const int bulk = lhbulk[t + 1];\n', '    const int bulk = lhbulk[t + 1], fs = fsplit_ok && t + 1 == SPL;\n', cnt=s.count('    const int bulk = lhbulk[t + 1];\n'))
rep('''    nodes[t]++;
    if (stopflag) return;
    if (SYM && sym_reject(t)) { symprune[t]++; return; }''',
'''    if (presplit) {                       // counted and split-checked by the parent (fast split)
        presplit = 0;
        if (stopflag) return;
        if (CHECK && LH && lh_reject(t)) { fprintf(stderr, "CHECK fast split at level %d\\n", t); exit(3); }
        goto past_split;
    }
    nodes[t]++;
    if (stopflag) return;
    if (SYM && sym_reject(t)) { symprune[t]++; return; }''')
rep('''    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }
    if (LVL[t].on) { search_fast(t); return; }''',
'''    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }
past_split:
    if (LVL[t].on) { search_fast(t); return; }''')
rep('    if (LH) build_lhbulk();\n', '    if (LH) build_lhbulk();\n', cnt=s.count('    if (LH) build_lhbulk();\n'))
rep('    if (LH) build_bulk();\n', '    if (LH) build_bulk();\n    fsplit_ok = SPL > 0 && SPL < NLEV && !SYM && !LR && !(LH && lhact[SPL]) && !getenv("LWE11NOFASTSPLIT");\n')
open(dst, 'w').write(s)
print('patched', dst)
