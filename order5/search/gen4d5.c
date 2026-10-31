// Generic case (A is an information set): C1 = {(a, aU)}, U unitary 7x7 over F16.
// Search rows of U (rows indexed by A-coordinates in order ORD).
// Symmetry used: D = mu5 row/column scalings (canonical form), GL(3,2)_B x Gal on row 0's class pattern,
// and GL(3,2)_A transitivity: row ORD[0] has the minimal orbit key among all 7 rows.
// Env: THRESH (default 16), PART=i, NPART=N (split depth-1 nodes), REP_ONLY=r.
#include "common.h"
#include <omp.h>

static const int ORD[7] = {0,1,3,2,4,5,6};
static int GL[168][7]; static int nGL=0;
static int THRESH=16;
static uint16_t KEY[1<<14];
static uint32_t *CORD[8]; static long NCORD[8];
static uint32_t *CHK[8]; static long NCHK[8];   // packed: combo index <<2 | class     // canonical (min-image) pattern index under GL(3,2) x swap(2<->3)

static int check_row_single(uint32_t v){
    if(hdot(v,v)!=1) return 0;
    for(int c=1;c<4;c++){
        uint32_t w=smul(REP[c],v);
        if(Mtab[pidx(w)] + (c==1?4:2) < THRESH) return 0;
    }
    return 1;
}
static int PAIR_L[45], PAIR_C[45];
static void init_pair_order(void){
    int n=0;
    for(int tgt=4; tgt<=8; tgt+=2)
        for(int l=1;l<16;l++) for(int c=1;c<4;c++)
            if(WT5[l]+(c==1?4:2)==tgt){ PAIR_L[n]=l; PAIR_C[n]=c; n++; }
    if(n!=45){ fprintf(stderr,"pair order error\n"); exit(1); }
}
static inline int pairOK(uint32_t v, uint32_t u){
    uint32_t uc[4]; uc[1]=smul(REP[1],u); uc[2]=smul(REP[2],u); uc[3]=smul(REP[3],u);
    for(int k=0;k<45;k++){
        int l=PAIR_L[k], c=PAIR_C[k];
        uint32_t b = smul(l,v) ^ uc[c];
        if(Mtab[pidx(b)] + WT5[l] + (c==1?4:2) < THRESH) return 0;
    }
    return 1;
}
static void gen_GL(void){
    int p[7]={0,1,2,3,4,5,6};
    int lineset[7]; for(int l=0;l<7;l++) lineset[l]=(1<<LINES[l][0])|(1<<LINES[l][1])|(1<<LINES[l][2]);
    while(1){
        int ok=1;
        for(int l=0;l<7&&ok;l++){
            int m=(1<<p[LINES[l][0]])|(1<<p[LINES[l][1]])|(1<<p[LINES[l][2]]);
            int f=0; for(int t=0;t<7;t++) if(lineset[t]==m) f=1;
            if(!f) ok=0;
        }
        if(ok){ memcpy(GL[nGL],p,sizeof p); nGL++; }
        int i=5; while(i>=0 && p[i]>p[i+1]) i--; if(i<0) break;
        int j=6; while(p[j]<p[i]) j--; int t=p[i];p[i]=p[j];p[j]=t;
        for(int a=i+1,b=6;a<b;a++,b--){t=p[a];p[a]=p[b];p[b]=t;}
    }
}
static void gen_keys(void){
    for(uint32_t p=0;p<(1u<<14);p++){
        uint32_t best=p;
        for(int g=0; g<nGL; g++) for(int sw=0; sw<2; sw++){
            uint32_t q=0;
            for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; if(sw && c>=2) c=5-c; q|=(uint32_t)c<<(2*GL[g][j]); }
            if(q<best) best=q;
        }
        KEY[p]=(uint16_t)best;
    }
}
typedef struct { uint8_t par[14]; } UF;
static inline int uf_find(UF *u, int x){ while(u->par[x]!=x) x=u->par[x]; return x; }
static inline int dnorm_ok(const UF *st, int depth, uint32_t row, UF *out){
    UF u=*st;
    for(int j=0;j<7;j++){
        int e=nib(row,j); if(!e) continue;
        int a=uf_find(&u,depth), b=uf_find(&u,7+j);
        if(a!=b){ if(e!=REP[CLS[e]]) return 0; u.par[a]=b; }
    }
    *out=u; return 1;
}
// Accept row u at depth d (given combos of rows 0..d-1); returns 1 if all codewords pass.
static void init_check_lists(void){
    // For depth d (placing row for coordinate ORD[d]), combos i over rows 0..d-1 (digit k = lambda for row k,
    // position ORD[k]); a = sum lambda_k e_ORD[k] + REP[c] e_ORD[d]. Keep pairs with >=2 nonzero digits
    // (weight 0/1 combos are guaranteed by R-membership and pairOK) and M_A <= THRESH-4
    // (M_B >= 2 always since partial rows are orthonormal hence independent), sorted by M_A ascending.
    for(int d=1; d<=6; d++){
        long n=1L<<(4*d);
        long cap=0; long cnt[40]={0};
        uint8_t *ma=malloc(n*4);
        for(long i=0;i<n;i++){
            int nz=0; uint32_t pa=0;
            for(int k=0;k<d;k++){ int l=(i>>(4*k))&15; if(l){ nz++; pa|=(uint32_t)CLS[l]<<(2*ORD[k]); } }
            for(int c=1;c<4;c++){
                int m = Mtab[pa | ((uint32_t)c<<(2*ORD[d]))];
                ma[i*4+c]= (nz>=2 && m<=THRESH-4) ? (uint8_t)m : 255;
                if(ma[i*4+c]!=255){ cnt[m]++; cap++; }
            }
        }
        CHK[d]=malloc((cap+1)*sizeof(uint32_t)); long q=0;
        for(int m=0;m<40;m++) if(cnt[m]) for(long i=0;i<n;i++) for(int c=1;c<4;c++) if(ma[i*4+c]==m) CHK[d][q++]=(uint32_t)(i<<2|c);
        NCHK[d]=q; free(ma);
    }
}
static void init_combo_order(void){
    for(int d=1; d<=6; d++){
        long n=1L<<(4*d); CORD[d]=malloc(n*sizeof(uint32_t)); long q=0;
        for(int w=2; w<=d; w++)
            for(long i=0;i<n;i++){ int nz=0; for(int k=0;k<d;k++) if((i>>(4*k))&15) nz++; if(nz==w) CORD[d][q++]=(uint32_t)i; }
        NCORD[d]=q;
    }
}
static inline int full_check(uint32_t u, int depth, const uint32_t *cB, const uint16_t *cPA, long ncombo){
    int sh=2*ORD[depth];
    const uint32_t *chk=CHK[depth]; long nchk=NCHK[depth]; (void)ncombo;
    uint32_t uc[4]; uc[0]=0; uc[1]=smul(REP[1],u); uc[2]=smul(REP[2],u); uc[3]=smul(REP[3],u);
    for(long k=0;k<nchk;k++){
        uint32_t e=chk[k]; long i=e>>2; int c=e&3;
        if(Mtab[cPA[i] | ((uint32_t)c<<sh)] + Mtab[pidx(cB[i]^uc[c])] < THRESH) return 0;
    }
    return 1;
}
static void dfs(int depth, uint32_t *rows, const uint32_t *cB, const uint16_t *cPA, long ncombo,
                const uint32_t *L, long nL, const UF *uf, long long *cnt, long long *sols);
// Try row u at 'depth'; pool = candidate pool for this depth (used to build the next pool).
static void step(int depth, uint32_t u, uint32_t *rows, const uint32_t *cB, const uint16_t *cPA, long ncombo,
                 const uint32_t *pool, long npool, const UF *uf, long long *cnt, long long *sols){
    UF nu;
    if(!dnorm_ok(uf,depth,u,&nu)) return;
    if(!full_check(u,depth,cB,cPA,ncombo)) return;
    cnt[depth+1]++;
    rows[depth]=u;
    if(depth==4){
        #pragma omp critical
        { printf("DEPTH5:"); for(int r=0;r<5;r++) printf(" %07x",rows[r]); printf("\n"); fflush(stdout); }
    }
    if(depth==6){
        (*sols)++;
        #pragma omp critical
        { printf("SOLUTION:"); for(int r=0;r<7;r++) printf(" %07x",rows[r]); printf("\n"); fflush(stdout); }
        return;
    }
    uint32_t *L2=malloc((npool+1)*sizeof(uint32_t)); long n2=0;
    for(long s=0;s<npool;s++){ uint32_t v=pool[s]; if(hdot(v,u)==0 && pairOK(u,v)) L2[n2++]=v; }
    if(n2>0){
        long nc2=ncombo*16;
        uint32_t *nB=malloc(nc2*sizeof(uint32_t)); uint16_t *nPA=malloc(nc2*sizeof(uint16_t));
        int sh=2*ORD[depth]; long q=0;
        for(int l=0;l<16;l++){
            uint32_t lu=smul(l,u); uint16_t add=(uint16_t)(CLS[l]<<sh);
            for(long i=0;i<ncombo;i++){ nB[q]=cB[i]^lu; nPA[q]=cPA[i]|add; q++; }
        }
        dfs(depth+1, rows, nB, nPA, nc2, L2, n2, &nu, cnt, sols);
        free(nB); free(nPA);
    }
    free(L2);
}
static void dfs(int depth, uint32_t *rows, const uint32_t *cB, const uint16_t *cPA, long ncombo,
                const uint32_t *L, long nL, const UF *uf, long long *cnt, long long *sols){
    for(long t=0;t<nL;t++) step(depth, L[t], rows, cB, cPA, ncombo, L, nL, uf, cnt, sols);
}
int main(int argc, char **argv){
    if(getenv("THRESH")) THRESH=atoi(getenv("THRESH"));
    long part = getenv("PART")?atol(getenv("PART")):0;
    long npart = getenv("NPART")?atol(getenv("NPART")):1;
    int reponly = getenv("REP_ONLY")?atoi(getenv("REP_ONLY")):-1;
    init_tables(); gen_GL(); gen_keys(); init_pair_order(); init_check_lists();
    double t0=omp_get_wtime();
    // R: all admissible rows
    uint32_t *R=malloc((size_t)(1u<<26)*sizeof(uint32_t)); long nR=0;
    for(uint32_t v=1; v<(1u<<28); v++) if(check_row_single(v)) R[nR++]=v;
    // reps (row-0 orbit representatives) sorted by key
    int nreps=0; uint32_t reps[4096]; uint16_t repkey[4096];
    for(uint32_t p=0;p<(1u<<14);p++){
        if(KEY[p]!=p) continue;
        uint32_t u=0; for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; u|=(uint32_t)REP[c]<<(4*j); }
        if(!check_row_single(u)) continue;
        repkey[nreps]=(uint16_t)p; reps[nreps++]=u;
    }
    // distribution of R over keys
    fprintf(stderr,"THRESH=%d |R|=%ld reps=%d PART=%ld/%ld (%.1fs)\n",THRESH,nR,nreps,part,npart,omp_get_wtime()-t0);
    for(int r=0;r<nreps;r++){ long c=0; for(long s=0;s<nR;s++) if(KEY[pidx(R[s])]==repkey[r]) c++;
        fprintf(stderr,"  rep %d key=%d u=%07x : %ld rows\n",r,repkey[r],reps[r],c); }
    long long tot[8]={0}; long long totsols=0;
    for(int r=0;r<nreps;r++){
        if(reponly>=0 && r!=reponly) continue;
        uint32_t u1=reps[r];
        double t1=omp_get_wtime();
        // candidates: rows with key >= key(rep r), orthogonal to u1, pair-OK with u1
        uint32_t *L1=malloc(nR*sizeof(uint32_t)); long n1=0;
        for(long s=0;s<nR;s++){ uint32_t v=R[s];
            if(KEY[pidx(v)]<repkey[r]) continue;
            { int e=0; for(int j=0;j<7;j++){ e=nib(v,j); if(e) break; } if(e!=REP[CLS[e]]) continue; }
            if(hdot(v,u1)==0 && pairOK(u1,v)) L1[n1++]=v; }
        UF uf; for(int i=0;i<14;i++) uf.par[i]=i;
        UF uf1; if(!dnorm_ok(&uf,0,u1,&uf1)){ fprintf(stderr,"rep not normalized?\n"); exit(1); }
        uint32_t cB[16]; uint16_t cPA[16];
        for(int l=0;l<16;l++){ cB[l]=smul(l,u1); cPA[l]=(uint16_t)(CLS[l]<<(2*ORD[0])); }
        long long cnt[8]={0}; long long ls=0;
        #pragma omp parallel
        {
            long long pc[8]={0}; long long ps=0; uint32_t rows[7]; rows[0]=u1;
            #pragma omp for schedule(dynamic,1)
            for(long t=0;t<n1;t++){
                if(((uint64_t)L1[t]*2654435761ULL>>7) % npart != part) continue;
                step(1, L1[t], rows, cB, cPA, 16, L1, n1, &uf1, pc, &ps);
            }
            #pragma omp critical
            { for(int d=0;d<8;d++) cnt[d]+=pc[d]; ls+=ps; }
        }
        cnt[1]=1;
        for(int d=0;d<8;d++) tot[d]+=cnt[d]; totsols+=ls;
        fprintf(stderr,"rep %d u1=%07x |L1|=%ld nodes:",r,u1,n1);
        for(int d=1;d<=7;d++) fprintf(stderr," %lld",cnt[d]);
        fprintf(stderr,"  sols=%lld (%.1fs)\n",ls,omp_get_wtime()-t1);
        free(L1);
    }
    fprintf(stderr,"TOTAL nodes per depth:");
    for(int d=1;d<=7;d++) fprintf(stderr," %lld",tot[d]);
    fprintf(stderr,"\nTOTAL solutions: %lld   time %.1fs\n",totsols,omp_get_wtime()-t0);
    return 0;
}
