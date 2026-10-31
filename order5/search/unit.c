#include "common.h"
// dump random packed vectors with pidx, hdot, smul results for python cross-check
int main(void){
    init_tables();
    uint64_t s=12345;
    for(int t=0;t<20000;t++){
        s^=s<<13; s^=s>>7; s^=s<<17; uint32_t u=(uint32_t)(s&0xFFFFFFF);
        s^=s<<13; s^=s>>7; s^=s<<17; uint32_t v=(uint32_t)(s&0xFFFFFFF);
        int l=(int)(s>>40)&15;
        printf("%u %u %d %u %u %u\n",u,v,l,pidx(u),hdot(u,v),smul(l,u));
    }
    return 0;
}
