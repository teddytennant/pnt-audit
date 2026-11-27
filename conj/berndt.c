// S(k) = sum_{h=1}^{k-1} sum_{j=1}^{k-1} (-1)^(j+1+floor(h j / k)), for primes k. Berndt-Bhat-Meyer-Xie-Zaharescu, arXiv:2501.03234.
#include <stdio.h>
#include <stdlib.h>
static int isp(long n){ if(n<2)return 0; for(long d=2;d*d<=n;d++) if(n%d==0)return 0; return 1; }
int main(int argc,char**argv){ long lo=atol(argv[1]),hi=atol(argv[2]); int np=0; long*P=malloc(sizeof(long)*(hi-lo+2));
  for(long k=lo;k<=hi;k++) if(isp(k)&&(k&1)) P[np++]=k;
  long long*R=malloc(sizeof(long long)*np);
  #pragma omp parallel for schedule(dynamic,4)
  for(int i=0;i<np;i++){ long k=P[i]; long long S=0;
    for(long h=1;h<k;h++){ long r=0; int par=0; long long s=0;        // par = parity of j+1+floor(hj/k)
      for(long j=1;j<k;j++){ r+=h; par^=1; if(r>=k){r-=k; par^=1;} s+= par? 1:-1; }   // j=1: j+1 even -> start par for j+1: handled below
      S+=s; }
    R[i]=S; }
  for(int i=0;i<np;i++) printf("%ld %lld\n",P[i],R[i]);
  return 0; }
