// gcc -O3 -o fast fast.c && ./fast 0x42D
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
uint64_t sm(uint64_t z){z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL;z=(z^(z>>27))*0x94D049BB133111EBULL;return z^(z>>31);}
int main(int c,char**v){
  uint64_t S=c>1?strtoull(v[1],0,16):0x42D;
  const char*s[]={"sRGB","clj-mcp","nrepl","grain","modex","fastmlx","Gay.jl","∞"};
  int sum=0;
  for(int i=0;i<8;i++){uint64_t st=sm(S^i);double h=(st%65536)/65536.0*360;int t=st%3-1;sum+=t;
    int r=128+127*cos((h-0)*M_PI/180),g=128+127*cos((h-120)*M_PI/180),b=128+127*cos((h-240)*M_PI/180);
    printf("\033[48;2;%d;%d;%dm  \033[0m %d %-12s %c\n",r,g,b,i,s[i],"-o+"[t+1]);}
  printf("sum=%dmod3\n",sum);return 0;}
