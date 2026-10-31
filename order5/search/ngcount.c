// Count super-heavy isotropic side vectors and k=1,2 structures for the non-generic case.
#include "common.h"
static int GL[168][7]; static int nGL=0;
static void gen_GL(void){
    int p[7]={0,1,2,3,4,5,6};
    int lineset[7]; for(int l=0;l<7;l++) lineset[l]=(1<<LINES[l][0])|(1<<LINES[l][1])|(1<<LINES[l][2]);
    while(1){ int ok=1;
        for(int l=0;l<7&&ok;l++){ int m=(1<<p[LINES[l][0]])|(1<<p[LINES[l][1]])|(1<<p[LINES[l][2]]);
            int f=0; for(int t=0;t<7;t++) if(lineset[t]==m) f=1; if(!f) ok=0; }
        if(ok){ memcpy(GL[nGL],p,sizeof p); nGL++; }
        int i=5; while(i>=0 && p[i]>p[i+1]) i--; if(i<0) break;
        int j=6; while(p[j]<p[i]) j--; int t=p[i];p[i]=p[j];p[j]=t;
        for(int a=i+1,b=6;a<b;a++,b--){t=p[a];p[a]=p[b];p[b]=t;} }
}
static int superheavy(uint32_t v){ for(int c=1;c<4;c++) if(Mtab[pidx(smul(REP[c],v))]<16) return 0; return 1; }
int main(void){
    init_tables(); gen_GL();
    long nS=0; uint32_t *S=malloc((1u<<28)/8*sizeof(uint32_t));
    for(uint32_t v=1; v<(1u<<28); v++) if(hdot(v,v)==0 && superheavy(v)) S[nS++]=v;
    printf("super-heavy isotropic vectors: %ld (1-dim subspaces: %ld)\n",nS,nS/15);
    // class-pattern orbits of 1-dim subspaces: rotations x GL x (Gal optional)
    static uint8_t seenA[1<<14], seenB[1<<14];
    int nA=0,nB=0; long hist[8]={0};
    for(long i=0;i<nS;i++){
        uint32_t p=pidx(S[i]);
        // canonical under rotation x GL x swap (A) and rotation x GL (B)
        uint32_t bestA=p,bestB=p;
        for(int rot=0;rot<3;rot++) for(int g=0;g<nGL;g++) for(int sw=0;sw<2;sw++){
            uint32_t q=0;
            for(int j=0;j<7;j++){ int c=(p>>(2*j))&3; if(c){ c=((c-1+rot)%3)+1; if(sw && c>=2) c=5-c; } q|=(uint32_t)c<<(2*GL[g][j]); }
            if(q<bestA) bestA=q; if(!sw && q<bestB) bestB=q;
        }
        if(!seenA[bestA]){ seenA[bestA]=1; nA++; }
        if(!seenB[bestB]){ seenB[bestB]=1; nB++; }
        int w=0; for(int j=0;j<7;j++) if(nib(S[i],j)) w++; hist[w]++;
    }
    printf("1-dim orbit reps: A-side (with Gal) %d, B-side (no Gal) %d\n",nA,nB);
    for(int w=0;w<8;w++) if(hist[w]) printf("  weight %d: %ld vectors\n",w,hist[w]);
    // k=2: count 2-dim self-orthogonal subspaces with all points super-heavy (all, labeled)
    // membership test via sorted array + bsearch
    long n2=0;
    // use a bitmap over 2^28 for S membership
    uint8_t *bm=calloc(1u<<25,1); for(long i=0;i<nS;i++) bm[S[i]>>3]|=1<<(S[i]&7);
    #define INS(v) ((bm[(v)>>3]>>((v)&7))&1)
    #pragma omp parallel for reduction(+:n2) schedule(dynamic,1024)
    for(long i=0;i<nS;i++){
        uint32_t v1=S[i];
        for(long j=0;j<nS;j++){
            uint32_t v2=S[j];
            if(v2<=v1) continue;            // count ordered pairs v1<v2 then divide
            if(hdot(v1,v2)) continue;
            int ok=1;
            for(int l=1;l<16 && ok;l++){ uint32_t w=smul(l,v1)^v2; if(!INS(w)) ok=0; }
            if(ok) n2++;
        }
    }
    // each 2-dim subspace has 255 nonzero vectors; number of ordered (v1<v2) spanning pairs = C(255,2)-?; report raw
    printf("pairs (v1<v2) spanning all-super-heavy self-orthogonal 2-spaces: %ld  -> subspaces ~ %ld\n", n2, n2/((255L*240)/2));
    return 0;
}
