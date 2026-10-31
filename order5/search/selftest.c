#include "common.h"
int main(void){
    init_tables();
    // dump tables for cross-check with python
    FILE *f=fopen("tables_c.txt","w");
    for(int a=0;a<16;a++){ for(int b=0;b<16;b++) fprintf(f,"%d ",MUL[a][b]); fprintf(f,"\n"); }
    for(int a=0;a<16;a++) fprintf(f,"%d %d %d %d\n",CONJ[a],NRM[a],CLS[a],WT5[a]);
    for(int i=0;i<(1<<14);i++) fprintf(f,"%d\n",Mtab[i]);
    fclose(f);
    printf("REP: %d %d %d ; NORMVAL %d %d %d\n",REP[1],REP[2],REP[3],NORMVAL[1],NORMVAL[2],NORMVAL[3]);
    // pair position-independence: 2-point supports
    int bad=0;
    for(int i=0;i<7;i++) for(int j=i+1;j<7;j++) for(int ci=1;ci<4;ci++) for(int cj=1;cj<4;cj++){
        uint32_t idx=0; idx|=ci<<(2*i); idx|=cj<<(2*j);
        int W=(ci==1?4:2)+(cj==1?4:2);
        if(Mtab[idx]!=W) bad++;
    }
    printf("pair M==W violations: %d\n",bad);
    // single
    for(int i=0;i<7;i++) for(int c=1;c<4;c++){ uint32_t idx=c<<(2*i); if(Mtab[idx]!=(c==1?4:2)) printf("single bad\n"); }
    int hist[40]={0}; for(int i=0;i<(1<<14);i++) hist[Mtab[i]]++;
    for(int m=0;m<40;m++) if(hist[m]) printf("M=%d: %d patterns\n",m,hist[m]);
    return 0;
}
