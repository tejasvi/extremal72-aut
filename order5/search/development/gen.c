// Generic case (A is an information set): C1 = {(a, aU)}, U unitary 7x7 over F16.
// Exhaustive search over U row by row (rows indexed by A-coordinates in order ORD),
// with D (mu5 row/column scaling) canonical form, row-1 orbit reps under GL(3,2)_B x Gal.
#include "common.h"
#include <time.h>
#include <omp.h>

static const int ORD[7] = {0,1,3,2,4,5,6};
static uint32_t *R; static long nR;
static int GL[168][7]; static int nGL=0;
static long long nodes[8];
static long long sols=0;

static int check_row_single(uint32_t v){
    if(hdot(v,v)!=1) return 0;
    for(int c=1;c<4;c++){
        uint32_t w=smul(REP[c],v);
        if(Mtab[pidx(w)] < 16 - (c==1?4:2)) return 0;
    }
    return 1;
}
static int pairOK(uint32_t v, uint32_t u){
    for(int l=1;l<16;l++){
        uint32_t lv=smul(l,v); int wl=WT5[l];
        for(int c=1;c<4;c++){
            uint32_t b = lv ^ smul(REP[c],u);
            if(Mtab[pidx(b)] + wl + (c==1?4:2) < 16) return 0;
        }
    }
    return 1;
}
static void gen_GL(void){
    int p[7]={0,1,2,3,4,5,6};
    // iterate permutations of 7 (Heap's algorithm via next_permutation)
    int lineset[7]; for(int l=0;l<7;l++) lineset[l]=(1<<LINES[l][0])|(1<<LINES[l][1])|(1<<LINES[l][2]);
    while(1){
        int ok=1;
        for(int l=0;l<7&&ok;l++){
            int m=(1<<p[LINES[l][0]])|(1<<p[LINES[l][1]])|(1<<p[LINES[l][2]]);
            int f=0; for(int t=0;t<7;t++) if(lineset[t]==m) f=1;
            if(!f) ok=0;
        }
        if(ok){ memcpy(GL[nGL],p,sizeof p); nGL++; }
        // next permutation
        int i=5; while(i>=0 && p[i]>p[i+1]) i--; if(i<0) break;
        int j=6; while(p[j]<p[i]) j--; int t=p[i];p[i]=p[j];p[j]=t;
        for(int a=i+1,b=6;a<b;a++,b--){t=p[a];p[a]=p[b];p[b]=t;}
    }
}
// union-find on 14 vars: 0..6 rows (by depth), 7..13 columns
typedef struct { uint8_t par[14]; } UF;
static int uf_find(UF *u, int x){ while(u->par[x]!=x) x=u->par[x]; return x; }
static int dnorm_ok(const UF *st, int depth, uint32_t row, UF *out){
    UF u=*st;
    for(int j=0;j<7;j++){
        int e=nib(row,j); if(!e) continue;
        int a=uf_find(&u,depth), b=uf_find(&u,7+j);
        if(a!=b){ if(e!=REP[CLS[e]]) return 0; u.par[a]=b; }
    }
    if(out) *out=u;
    return 1;
}
typedef struct {
    uint32_t rows[7];
    uint32_t *cB; uint16_t *cPA; long ncombo;   // combos of chosen rows
} State;

static void dfs(int depth, uint32_t *rows, uint32_t *cB, uint16_t *cPA, long ncombo,
                uint32_t *L, long nL, const UF *uf, long long *lnodes, long long *lsols){
    // choose row for depth (A coordinate ORD[depth]) from candidate list L
    int pos=ORD[depth];
    uint32_t sh = 2*pos;
    for(long t=0;t<nL;t++){
        uint32_t u=L[t]; UF nu;
        if(!dnorm_ok(uf,depth,u,&nu)) continue;
        // full check over combos (a' + REP[c] e_pos)
        int ok=1;
        uint32_t uc[4]; for(int c=1;c<4;c++) uc[c]=smul(REP[c],u);
        for(long i=0;i<ncombo && ok;i++){
            uint32_t b0=cB[i]; uint32_t pa=cPA[i];
            for(int c=1;c<4;c++){
                uint32_t b=b0^uc[c];
                if(Mtab[pa | (c<<sh)] + Mtab[pidx(b)] < 16){ ok=0; break; }
            }
        }
        if(!ok) continue;
        lnodes[depth+1]++;
        rows[depth]=u;
        if(depth==6){ (*lsols)++;
            #pragma omp critical
            { printf("SOLUTION:"); for(int r=0;r<7;r++) printf(" %07x",rows[r]); printf("\n"); fflush(stdout);} 
            continue; }
        // new combos
        long nc2=ncombo*16;
        uint32_t *nB=malloc(nc2*sizeof(uint32_t)); uint16_t *nPA=malloc(nc2*sizeof(uint16_t));
        long q=0;
        for(int l=0;l<16;l++){
            uint32_t lu=smul(l,u); uint32_t add=(uint32_t)CLS[l]<<sh;
            for(long i=0;i<ncombo;i++){ nB[q]=cB[i]^lu; nPA[q]=cPA[i]|add; q++; }
        }
        // filter candidate list
        uint32_t *L2=malloc((nL+1)*sizeof(uint32_t)); long n2=0;
        for(long s=0;s<nL;s++){ uint32_t v=L[s]; if(hdot(v,u)==0 && pairOK(u,v)) L2[n2++]=v; }
        dfs(depth+1, rows, nB, nPA, nc2, L2, n2, &nu, lnodes, lsols);
        free(L2); free(nB); free(nPA);
    }
}
int main(int argc, char **argv){
    init_tables(); gen_GL();
    fprintf(stderr,"GL(3,2) size %d\n",nGL);
    double t0=omp_get_wtime();
    // build R
    R=malloc((size_t)(1u<<28)/4*sizeof(uint32_t)); nR=0;
    for(uint32_t v=1; v<(1u<<28); v++) if(check_row_single(v)) R[nR++]=v;
    fprintf(stderr,"|R| = %ld  (%.1fs)\n",nR,omp_get_wtime()-t0);
    // level-1 reps: class patterns
    int nreps=0; uint32_t reps[4096];
    for(uint32_t p=0;p<(1u<<14);p++){
        uint32_t u=0; for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; u|=(uint32_t)REP[c]<<(4*j); }
        if(!check_row_single(u)) continue;
        // canonical: minimal among images under GL x swap(2<->3)
        int minimal=1;
        for(int g=0; g<nGL && minimal; g++) for(int sw=0; sw<2 && minimal; sw++){
            uint32_t q=0;
            for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; if(sw && c>=2) c=5-c; q|=(uint32_t)c<<(2*GL[g][j]); }
            if(q<p) minimal=0;
        }
        if(minimal) reps[nreps++]=u;
    }
    fprintf(stderr,"level-1 orbit reps: %d\n",nreps);
    long long tot[8]={0}; long long totsols=0;
    long smod = getenv("SAMPLE_MOD")?atol(getenv("SAMPLE_MOD")):1;
    long sres = getenv("SAMPLE_RES")?atol(getenv("SAMPLE_RES")):0;
    int reponly = getenv("REP_ONLY")?atoi(getenv("REP_ONLY")):-1;
    for(int r=0;r<nreps;r++){
        if(reponly>=0 && r!=reponly) continue;
        uint32_t u1=reps[r];
        double t1=omp_get_wtime();
        // candidates for depth 1: R filtered by u1
        uint32_t *L1=malloc(nR*sizeof(uint32_t)); long n1=0;
        for(long s=0;s<nR;s++){ uint32_t v=R[s]; if(hdot(v,u1)==0 && pairOK(u1,v)) L1[n1++]=v; }
        UF uf; for(int i=0;i<14;i++) uf.par[i]=i;
        UF uf1; if(!dnorm_ok(&uf,0,u1,&uf1)){ fprintf(stderr,"rep not normalized?\n"); exit(1); }
        // combos for depth 1
        uint32_t cB[16]; uint16_t cPA[16];
        for(int l=0;l<16;l++){ cB[l]=smul(l,u1); cPA[l]=(uint16_t)(CLS[l]<<(2*ORD[0])); }
        // parallel over depth-1 candidates
        long long ln[8]={0}; long long ls=0;
        #pragma omp parallel
        {
            long long pn[8]={0}; long long ps=0;
            uint32_t rows[7]; rows[0]=u1;
            #pragma omp for schedule(dynamic,1)
            for(long t=0;t<n1;t++){
                if(t % smod != sres) continue;
                uint32_t one[1]={L1[t]};
                // To keep candidate lists correct, run dfs with the single-element list at depth 1,
                // but pass the full L1 for further filtering: emulate by doing depth-1 step inline.
                uint32_t u=L1[t]; UF nu;
                if(!dnorm_ok(&uf1,1,u,&nu)) continue;
                int ok=1; int sh=2*ORD[1];
                for(int i=0;i<16&&ok;i++) for(int c=1;c<4;c++){
                    uint32_t b=cB[i]^smul(REP[c],u);
                    if(Mtab[cPA[i]|(c<<sh)]+Mtab[pidx(b)]<16){ok=0;break;}
                }
                if(!ok) continue;
                pn[2]++;
                rows[1]=u;
                uint32_t nB[256]; uint16_t nPA[256]; int q=0;
                for(int l=0;l<16;l++){ uint32_t lu=smul(l,u); uint16_t add=(uint16_t)(CLS[l]<<sh);
                    for(int i=0;i<16;i++){ nB[q]=cB[i]^lu; nPA[q]=cPA[i]|add; q++; } }
                uint32_t *L2=malloc((n1+1)*sizeof(uint32_t)); long n2=0;
                for(long s=0;s<n1;s++){ uint32_t v=L1[s]; if(hdot(v,u)==0 && pairOK(u,v)) L2[n2++]=v; }
                dfs(2, rows, nB, nPA, 256, L2, n2, &nu, pn, &ps);
                free(L2);
                (void)one;
            }
            #pragma omp critical
            { for(int d=0;d<8;d++) ln[d]+=pn[d]; ls+=ps; }
        }
        ln[1]=1;
        for(int d=0;d<8;d++) tot[d]+=ln[d]; totsols+=ls;
        fprintf(stderr,"rep %d/%d u1=%07x |L1|=%ld (sample 1/%ld) nodes:",r+1,nreps,u1,n1,smod);
        for(int d=1;d<=7;d++) fprintf(stderr," %lld",ln[d]);
        fprintf(stderr,"  sols=%lld (%.1fs)\n",ls,omp_get_wtime()-t1);
        free(L1);
    }
    fprintf(stderr,"TOTAL nodes per depth:");
    for(int d=1;d<=7;d++) fprintf(stderr," %lld",tot[d]);
    fprintf(stderr,"\nTOTAL solutions (generic case): %lld   time %.1fs\n",totsols,omp_get_wtime()-t0);
    return 0;
}
