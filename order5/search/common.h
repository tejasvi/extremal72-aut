// Common tables for the C5 case of the [72,36,16] problem.
// F16 = F2[x]/(x^4+x^3+x^2+x+1); element = 4-bit int, bit k = coeff of x^k.
#pragma once
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t MUL[16][16], CONJ[16], NRM[16], CLS[16], WT5[16], INV[16];
static uint8_t REP[4];            // REP[c] = representative of norm class c (c=1,2,3); REP[0]=0
static uint8_t NORMVAL[4];        // F4 value of class c (as F16 element)
static const int LINES[7][3] = {{0,1,3},{1,2,4},{2,3,5},{3,4,6},{4,5,0},{5,6,1},{6,0,2}};
static uint8_t Mtab[1<<14];       // side function on class patterns (base 4, coord j -> digit j)
static uint8_t P8[256];           // two nibbles -> two class digits (4 bits)
static uint8_t HD2[256][256];     // Hermitian product of two 2-nibble chunks
static uint8_t SMB[16][256];      // scalar * byte (2 nibbles)

static uint8_t gmul(uint8_t a, uint8_t b){
    uint16_t r=0; for(int i=0;i<4;i++) if((b>>i)&1) r^=(uint16_t)a<<i;
    for(int d=7; d>=4; d--) if((r>>d)&1) r^=0x1F<<(d-4);
    return (uint8_t)r;
}
static int hval(const int *S, int ns, int x, const int *w){
    int in[7]={0}; for(int t=0;t<ns;t++) in[S[t]]=1;
    int h=5*ns+x; for(int i=0;i<7;i++) h += in[i]? -w[i] : w[i];
    return h;
}
static int Mside_w(const int *w){
    int best=1000, S[7], ns;
    best = hval(S,0,0,w);
    for(int l=0;l<7;l++){
        ns=0; for(int t=0;t<3;t++) S[ns++]=LINES[l][t];
        int h=hval(S,ns,1,w); if(h<best) best=h;
        ns=0; for(int i=0;i<7;i++){int on=0; for(int t=0;t<3;t++) if(LINES[l][t]==i) on=1; if(!on) S[ns++]=i;}
        h=hval(S,ns,0,w); if(h<best) best=h;
    }
    ns=0; for(int i=0;i<7;i++) S[ns++]=i;
    int h=hval(S,ns,1,w); if(h<best) best=h;
    return best;
}
static void init_tables(void){
    for(int a=0;a<16;a++) for(int b=0;b<16;b++) MUL[a][b]=gmul(a,b);
    for(int a=0;a<16;a++){
        uint8_t p=1; for(int e=0;e<4;e++) p=MUL[p][a]; CONJ[a]=p;      // a^4
        p=1; for(int e=0;e<5;e++) p=MUL[p][a]; NRM[a]=p;               // a^5
        INV[a]=0; for(int b=1;b<16;b++) if(MUL[a][b]==1) INV[a]=b;
    }
    // F4 = {0,1,w,w^2}: pick w = smallest norm value not 0/1
    uint8_t w=0; for(int a=1;a<16;a++) if(NRM[a]!=1){ w=NRM[a]; break; }
    uint8_t w2=MUL[w][w];
    for(int a=0;a<16;a++){
        if(a==0) CLS[a]=0; else if(NRM[a]==1) CLS[a]=1; else if(NRM[a]==w) CLS[a]=2; else if(NRM[a]==w2) CLS[a]=3;
        else { fprintf(stderr,"norm error\n"); exit(1); }
    }
    NORMVAL[0]=0; NORMVAL[1]=1; NORMVAL[2]=w; NORMVAL[3]=w2;
    REP[0]=0; for(int c=1;c<4;c++){ for(int a=1;a<16;a++) if(CLS[a]==c){ REP[c]=a; break; } }
    for(int a=0;a<16;a++) WT5[a] = a==0?0:(CLS[a]==1?4:2);
    for(int idx=0; idx<(1<<14); idx++){
        int wv[7]; int t=idx; for(int j=0;j<7;j++){ int c=t&3; t>>=2; wv[j]= c==0?0:(c==1?4:2); }
        Mtab[idx]=(uint8_t)Mside_w(wv);
    }
    for(int b=0;b<256;b++) P8[b] = CLS[b&15] | (CLS[b>>4]<<2);
    for(int a=0;a<256;a++) for(int b=0;b<256;b++)
        HD2[a][b] = MUL[a&15][CONJ[b&15]] ^ MUL[a>>4][CONJ[b>>4]];
    for(int s=0;s<16;s++) for(int b=0;b<256;b++) SMB[s][b] = MUL[s][b&15] | (MUL[s][b>>4]<<4);
}
static inline uint32_t pidx(uint32_t v){   // class pattern index of packed 7-nibble vector
    return P8[v&255] | (P8[(v>>8)&255]<<4) | (P8[(v>>16)&255]<<8) | ((uint32_t)CLS[(v>>24)&15]<<12);
}
static inline uint8_t hdot(uint32_t u, uint32_t v){
    return HD2[u&255][v&255] ^ HD2[(u>>8)&255][(v>>8)&255] ^ HD2[(u>>16)&255][(v>>16)&255]
         ^ MUL[(u>>24)&15][CONJ[(v>>24)&15]];
}
static inline uint32_t smul(uint8_t s, uint32_t v){
    return SMB[s][v&255] | ((uint32_t)SMB[s][(v>>8)&255]<<8) | ((uint32_t)SMB[s][(v>>16)&255]<<16)
         | ((uint32_t)MUL[s][(v>>24)&15]<<24);
}
static inline int nib(uint32_t v, int j){ return (v>>(4*j))&15; }
