// Zhi-Wei Sun's conjectures on a(n) = sum_{k<=n} (-1)^(k-Omega(k)) and b(n) = sum_{k<=n} (-1)^(k-Omega(k))/k  (OEIS A212496).
//  1: a(n) > 0 for n > 4            2: a(n) > sqrt n for n > 324          3: a(n) < sqrt n loglog n for n > 5892
//  4: b(n) < 0                      5: b(n) < -1/sqrt n for n > 1         6: b(n) > -loglog n/sqrt n for n > 2008
// usage: sun N     prints the first failure of each, and per-range extremes of a/sqrt n and b sqrt n
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <omp.h>
#define B (1<<20)
int main(int argc,char**argv){ uint64_t N=(uint64_t)atof(argv[1]); uint64_t r=(uint64_t)sqrtl((long double)N)+1;
  char*sm=calloc(r+1,1); uint64_t*pr=malloc(8*(r/2+10)); int np=0;
  for(uint64_t i=2;i<=r;i++){ if(!sm[i]){pr[np++]=i; for(uint64_t j=i*i;j<=r;j+=i)sm[j]=1;} }
  int T=omp_get_max_threads(); unsigned char**par=malloc(sizeof(void*)*T); uint64_t**prod=malloc(sizeof(void*)*T);
  for(int t=0;t<T;t++){par[t]=malloc(B);prod[t]=malloc(8*(size_t)B);}
  long long a=0; long double b=0; uint64_t first[7]={0}; double amin=1e300,amax=-1e300,bmin=1e300,bmax=-1e300; uint64_t amin_n=0,amax_n=0,bmin_n=0,bmax_n=0, next=1000;
  for(uint64_t base=1; base<=N; base+=(uint64_t)T*B){
    #pragma omp parallel for schedule(static,1)
    for(int t=0;t<T;t++){ uint64_t lo=base+(uint64_t)t*B; if(lo>N) continue; unsigned char*pa=par[t]; uint64_t*pd=prod[t];
      memset(pa,0,B); for(int i=0;i<B;i++)pd[i]=1;
      for(int i=0;i<np;i++){ uint64_t p=pr[i]; if(p*p>lo+B) break;
        for(uint64_t q=p;;q*=p){ uint64_t m=((lo+q-1)/q)*q; for(;m<lo+B;m+=q){ pa[m-lo]^=1; pd[m-lo]*=p; } if(q>(lo+B)/p) break; } }
      for(int i=0;i<B;i++) if(pd[i]!=lo+i) pa[i]^=1; }
    for(int t=0;t<T;t++){ uint64_t lo=base+(uint64_t)t*B; if(lo>N) break; unsigned char*pa=par[t];
      for(int i=0;i<B;i++){ uint64_t n=lo+i; if(n>N) break; int s=((n+pa[i])&1)?-1:1; a+=s; b+=(long double)s/(long double)n;
        double sq=sqrt((double)n); double ra=(double)a/sq, rb=(double)(b*sq);
        if(n>5892){ if(ra<amin){amin=ra;amin_n=n;} if(ra>amax){amax=ra;amax_n=n;} if(rb<bmin){bmin=rb;bmin_n=n;} if(rb>bmax){bmax=rb;bmax_n=n;} }
        if(!first[1]&&n>4&&a<=0) first[1]=n;
        if(!first[2]&&n>324&&ra<=1.0) first[2]=n;
        if(!first[4]&&b>=0) first[4]=n;
        if(!first[5]&&n>1&&rb>=-1.0) first[5]=n;
        if(n>5892 && (ra>2.0||rb<-2.0)){ double ll=log(log((double)n)); if(!first[3]&&ra>=ll) first[3]=n; if(!first[6]&&n>2008&&rb<=-ll) first[6]=n; }
        if(n==next||n==N){ printf("n<=%.3g: a/sqrt(n) in [%.4f @%llu, %.4f @%llu]  b*sqrt(n) in [%.4f @%llu, %.4f @%llu]  loglog=%.3f  a=%lld\n",(double)n,amin,(unsigned long long)amin_n,amax,(unsigned long long)amax_n,bmin,(unsigned long long)bmin_n,bmax,(unsigned long long)bmax_n,log(log((double)n)),a); fflush(stdout); next*=10; } } } }
  for(int c=1;c<=6;c++) printf("conjecture %d: %s%llu\n",c,first[c]?"FIRST FAILURE at n=":"no failure up to ",(unsigned long long)(first[c]?first[c]:N));
  return 0; }
