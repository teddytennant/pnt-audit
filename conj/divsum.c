// OEIS A245211: a(n) = sum_{d|n, d<n} d tau(d) = n only for n = 21?   OEIS A245212: n tau(n) - a(n) = sigma(n) only for powers of 2?
// f(n) = sum_{d|n} d tau(d) is multiplicative with f(p^e) = sum_{j<=e} (j+1) p^j.  usage: divsum N
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <omp.h>
#define B (1<<19)
int main(int argc,char**argv){ uint64_t N=(uint64_t)atof(argv[1]); uint64_t r=(uint64_t)sqrtl((long double)N)+1;
  char*sm=calloc(r+1,1); uint64_t*pr=malloc(8*(r/2+10)); int np=0;
  for(uint64_t i=2;i<=r;i++){ if(!sm[i]){pr[np++]=i; for(uint64_t j=i*i;j<=r;j+=i)sm[j]=1;} }
  uint64_t nseg=(N+B)/B;
  #pragma omp parallel
  { uint64_t*rem=malloc(8*(size_t)B),*f=malloc(8*(size_t)B),*sg=malloc(8*(size_t)B); uint32_t*tau=malloc(4*(size_t)B);
    #pragma omp for schedule(dynamic,8)
    for(uint64_t s=0;s<nseg;s++){ uint64_t lo=s*B+1;
      for(int i=0;i<B;i++){rem[i]=lo+i;f[i]=1;sg[i]=1;tau[i]=1;}
      for(int i=0;i<np;i++){ uint64_t p=pr[i]; if(p*p>lo+B) break;
        for(uint64_t m=((lo+p-1)/p)*p; m<lo+B; m+=p){ int k=m-lo; uint64_t x=rem[k]; int e=0; uint64_t pj=1, ff=1, ss=1;
          while(x%p==0){ x/=p; e++; pj*=p; ff+=(uint64_t)(e+1)*pj; ss+=pj; }
          rem[k]=x; f[k]*=ff; sg[k]*=ss; tau[k]*=(e+1); } }
      for(int i=0;i<B;i++){ uint64_t n=lo+i; if(n>N) break; uint64_t q=rem[i]; uint64_t F=f[i],S=sg[i]; uint32_t t=tau[i];
        if(q>1){ F*=(1+2*q); S*=(1+q); t*=2; }
        if(F==n*(uint64_t)(t+1)){
          #pragma omp critical
          { printf("A245211: a(n) = n at n = %llu\n",(unsigned long long)n); fflush(stdout);} }
        if(2*n*(uint64_t)t==F+S && (n&(n-1))!=0){
          #pragma omp critical
          { printf("A245212: n tau(n) - a(n) = sigma(n) at n = %llu, not a power of 2\n",(unsigned long long)n); fflush(stdout);} } } }
  }
  printf("searched n <= %llu\n",(unsigned long long)N); return 0; }
