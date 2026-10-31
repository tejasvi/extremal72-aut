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

// ---------- planted-solution soundness test ----------
static uint64_t rs=88172645463325252ULL;
static inline uint64_t xr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static int rand_unitary(uint32_t *U){
    for(int k=0;k<7;k++){
        for(long tries=0;;tries++){
            uint32_t v=(uint32_t)(xr()&0xFFFFFFF);
            if(hdot(v,v)!=1) continue;
            int ok=1; for(int i=0;i<k;i++) if(hdot(v,U[i])) { ok=0; break; }
            if(ok){ U[k]=v; break; }
        }
    }
    return 1;
}
// U[i] = row for A-coordinate i (natural order). Check all codewords a!=0.
static int full_code_ok(const uint32_t *U, int T){
    // iterate a over F16^7 via gray-like accumulation: b = sum a_i U[i]
    static uint32_t pre[7][16];
    for(int i=0;i<7;i++) for(int l=0;l<16;l++) pre[i][l]=smul(l,U[i]);
    long bad=0;
    #pragma omp parallel for reduction(+:bad) schedule(static)
    for(uint32_t hi=0; hi<(1u<<12); hi++){   // digits 4..6 (12 bits) outer, 0..3 inner
        uint32_t bhi=pre[4][hi&15]^pre[5][(hi>>4)&15]^pre[6][(hi>>8)&15];
        uint32_t pahi=((uint32_t)CLS[hi&15]<<8)|((uint32_t)CLS[(hi>>4)&15]<<10)|((uint32_t)CLS[(hi>>8)&15]<<12);
        for(uint32_t lo=0; lo<(1u<<16); lo++){
            if(hi==0 && lo==0) continue;
            uint32_t b=bhi^pre[0][lo&15]^pre[1][(lo>>4)&15]^pre[2][(lo>>8)&15]^pre[3][(lo>>12)&15];
            uint32_t pa=pahi|CLS[lo&15]|((uint32_t)CLS[(lo>>4)&15]<<2)|((uint32_t)CLS[(lo>>8)&15]<<4)|((uint32_t)CLS[(lo>>12)&15]<<6);
            if(Mtab[pa]+Mtab[pidx(b)]<T) bad++;
        }
    }
    return bad==0;
}
static uint8_t FROB(uint8_t x){ return MUL[x][x]; }
// Canonicalize U (natural row order) into search form W[depth] (rows in ORD order). Returns rep index or -1.
static int canonicalize(const uint32_t *U, uint32_t *W, const uint16_t *repkey, int nreps){
    // 1) choose P_A in GL(3,2) moving a min-key row to coordinate ORD[0]=0
    int kmin=1<<30; for(int i=0;i<7;i++){ int k=KEY[pidx(U[i])]; if(k<kmin) kmin=k; }
    int gA=-1;
    for(int g=0; g<nGL && gA<0; g++){ // row i moves to coordinate GL[g][i]; need row with min key at 0
        for(int i=0;i<7;i++) if(GL[g][i]==0 && KEY[pidx(U[i])]==kmin){ gA=g; break; }
    }
    uint32_t V[7]; for(int i=0;i<7;i++) V[GL[gA][i]]=U[i];
    // 2) P_B x Gal: bring row 0 pattern to KEY
    uint32_t p=pidx(V[0]); int gB=-1, swB=0;
    for(int g=0; g<nGL && gB<0; g++) for(int sw=0; sw<2; sw++){
        uint32_t q=0; for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; if(sw && c>=2) c=5-c; q|=(uint32_t)c<<(2*GL[g][j]); }
        if(q==KEY[p]){ gB=g; swB=sw; break; }
    }
    uint32_t X[7];
    for(int i=0;i<7;i++){ uint32_t r=0; for(int j=0;j<7;j++){ uint8_t e=nib(V[i],j); if(swB) e=FROB(e); r|=(uint32_t)e<<(4*GL[gB][j]); } X[i]=r; }
    if(pidx(X[0])!=KEY[p]){ fprintf(stderr,"canon: pattern mismatch\n"); return -1; }
    // 3) D-normalization in depth order (rows ORD[0..6]), row-major
    uint8_t M[7][7]; for(int d=0;d<7;d++) for(int j=0;j<7;j++) M[d][j]=nib(X[ORD[d]],j);
    int comp[14]; for(int v=0;v<14;v++) comp[v]=v;   // explicit component labels
    for(int d=0;d<7;d++) for(int j=0;j<7;j++){
        uint8_t e=M[d][j]; if(!e) continue;
        int cr=comp[d], cc=comp[7+j];
        if(cr==cc) continue;
        // find t in mu5 with e*t = REP[CLS[e]]; scale component cc: columns *t, rows *t^-1
        uint8_t t=0; for(uint8_t z=1;z<16;z++) if(CLS[z]==1 && MUL[e][z]==REP[CLS[e]]) t=z;
        uint8_t ti=INV[t];
        for(int jj=0;jj<7;jj++) if(comp[7+jj]==cc) for(int dd=0;dd<7;dd++) M[dd][jj]=MUL[M[dd][jj]][t];
        for(int dd=0;dd<7;dd++) if(comp[dd]==cc) for(int jj=0;jj<7;jj++) M[dd][jj]=MUL[M[dd][jj]][ti];
        for(int v=0;v<14;v++) if(comp[v]==cc) comp[v]=cr;
        if(M[d][j]!=REP[CLS[e]]){ fprintf(stderr,"canon: scaling error\n"); return -1; }
    }
    for(int d=0;d<7;d++){ uint32_t r=0; for(int j=0;j<7;j++) r|=(uint32_t)M[d][j]<<(4*j); W[d]=r; }
    for(int r=0;r<nreps;r++) if(repkey[r]==KEY[pidx(W[0])]) return r;
    return -1;
}
int main(int argc, char **argv){
    THRESH = getenv("THRESH")?atoi(getenv("THRESH")):12;
    int ntests = getenv("NTESTS")?atoi(getenv("NTESTS")):20;
    if(getenv("SEED")) rs=strtoull(getenv("SEED"),0,10);
    init_tables(); gen_GL(); gen_keys(); init_pair_order(); init_check_lists();
    // reps
    int nreps=0; uint32_t reps[4096]; uint16_t repkey[4096];
    for(uint32_t p=0;p<(1u<<14);p++){
        if(KEY[p]!=p) continue;
        uint32_t u=0; for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; u|=(uint32_t)REP[c]<<(4*j); }
        if(!check_row_single(u)) continue;
        repkey[nreps]=(uint16_t)p; reps[nreps++]=u;
    }
    fprintf(stderr,"THRESH=%d reps=%d\n",THRESH,nreps);
    int found=0, passed=0; long tried=0;
    while(found<ntests){
        uint32_t U[7]; rand_unitary(U); tried++;
        if(!full_code_ok(U,THRESH)) continue;
        found++;
        uint32_t W[7]; int r=canonicalize(U,W,repkey,nreps);
        if(r<0){ fprintf(stderr,"test %d: canonicalize failed\n",found); continue; }
        // sanity: canonical W must still define a valid code (in natural coordinate order)
        uint32_t Wn[7]; for(int d=0;d<7;d++) Wn[ORD[d]]=W[d];
        if(!full_code_ok(Wn,THRESH)){ fprintf(stderr,"test %d: canonical form NOT valid (bug in canon)\n",found); continue; }
        // trace through the search filters
        const char *fail=0; int fdepth=-1;
        if(W[0]!=reps[r]){ fail="row0 != rep"; fdepth=0; }
        UF uf; for(int i=0;i<14;i++) uf.par[i]=i; UF cur;
        if(!fail && !dnorm_ok(&uf,0,W[0],&cur)){ fail="dnorm row0"; fdepth=0; }
        uint32_t *cB=malloc((1L<<24)*sizeof(uint32_t)); uint16_t *cPA=malloc((1L<<24)*sizeof(uint16_t));
        uint32_t *nB=malloc((1L<<24)*sizeof(uint32_t)); uint16_t *nP=malloc((1L<<24)*sizeof(uint16_t));
        long nc=16;
        for(int l=0;l<16;l++){ cB[l]=smul(l,W[0]); cPA[l]=(uint16_t)(CLS[l]<<(2*ORD[0])); }
        for(int d=1; d<7 && !fail; d++){
            uint32_t u=W[d];
            if(!check_row_single(u)){ fail="not in R"; fdepth=d; break; }
            if(KEY[pidx(u)]<repkey[r]){ fail="key order"; fdepth=d; break; }
            { int e=0; for(int j=0;j<7;j++){ e=nib(u,j); if(e) break; } if(e!=REP[CLS[e]]){ fail="first-nonzero not rep"; fdepth=d; break; } }
            for(int k=0;k<d;k++){ if(hdot(u,W[k])){ fail="not orthogonal"; fdepth=d; break; } if(!pairOK(W[k],u)){ fail="pairOK"; fdepth=d; break; } }
            if(fail) break;
            UF nu; if(!dnorm_ok(&cur,d,u,&nu)){ fail="dnorm"; fdepth=d; break; }
            if(!full_check(u,d,cB,cPA,nc)){ fail="full_check"; fdepth=d; break; }
            cur=nu;
            if(d<6){
                long q=0; int sh=2*ORD[d];
                for(int l=0;l<16;l++){ uint32_t lu=smul(l,u); uint16_t add=(uint16_t)(CLS[l]<<sh);
                    for(long i=0;i<nc;i++){ nB[q]=cB[i]^lu; nP[q]=cPA[i]|add; q++; } }
                uint32_t *tb=cB; cB=nB; nB=tb; uint16_t *tp=cPA; cPA=nP; nP=tp; nc=q;
            }
        }
        free(cB); free(cPA); free(nB); free(nP);
        if(fail){ fprintf(stderr,"test %d (tried %ld): REJECTED at depth %d: %s\n",found,tried,fdepth,fail); }
        else { passed++; fprintf(stderr,"test %d (tried %ld): planted code accepted at ALL depths 0..6 (rep %d)\n",found,tried,r); }
    }
    fprintf(stderr,"planted tests: %d/%d accepted\n",passed,found);
    return passed==found?0:1;
}
