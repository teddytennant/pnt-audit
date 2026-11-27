// Colton's conjecture: T(n) >= pi(n)/2 for all n, where T(n) counts refactorable ("tau") numbers k <= n, tau(k) | k.
// Zelinsky (J. Integer Seq. 5 (2002), 02.2.8, Theorem 8) proved it for n > 7.42e13. This checks every n below that.
//
// 1. Pointwise for n <= X0, by a sieve of tau(n): pi(n) <= 2 T(n) at every n.
// 2. Above X0, on a chain x_0 = X0 < x_1 < ... : if pi(x_{k+1}) <= 2 L(x_k), where L(x) <= T(x), then for x_k <= n <= x_{k+1}
//    pi(n) <= pi(x_{k+1}) <= 2 L(x_k) <= 2 T(x_k) <= 2 T(n).
//    L(x) = sum over g <= G0 with 2 tau(g) | g of max(0, pi(x/g) - pi(P(g))), P(g) the largest prime factor of g.
//    Each such g and prime p > P(g) with g p <= x gives a refactorable g p (tau(gp) = 2 tau(g) divides g), and g p determines (g, p).
//    pi(x), pi(x/g) and pi(v) for v <= sqrt x are exact, from the Lucy_Hedgehog recurrence.
// usage: colton X0 XMAX RHO     (G0 = X0)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64; typedef uint32_t u32;
#define B (1<<16)
static u32*gen_g,*gen_p; static size_t ngen=0,capgen=0;
static void lucy(u64 x,u64 r,u64*sm,u64*lg){ // sm[v]=pi(v) for v<=r, lg[i]=pi(x/i) for 1<=i<=r
  for(u64 v=0;v<=r;v++) sm[v]= v? v-1:0; for(u64 i=1;i<=r;i++) lg[i]=x/i-1;
  for(u64 p=2;p<=r;p++){ if(sm[p]==sm[p-1]) continue; u64 sp=sm[p-1], p2=p*p; if(p2>x) break;
    u64 lim = x/p2 < r ? x/p2 : r;
    for(u64 i=1;i<=lim;i++){ u64 d=i*p; lg[i] -= (d<=r ? lg[d] : sm[x/d]) - sp; }
    for(u64 v=r; v>=p2; v--) sm[v] -= sm[v/p]-sp; } }
int main(int argc,char**argv){ u64 X0=(u64)atof(argv[1]), XMAX=(u64)atof(argv[2]); double RHO=atof(argv[3]);
  u64 r0=(u64)sqrtl((long double)X0)+1; char*c=calloc(r0+1,1); u64*pr=malloc(8*(r0/2+10)); int np=0;
  for(u64 i=2;i<=r0;i++){ if(!c[i]){pr[np++]=i; for(u64 j=i*i;j<=r0;j+=i)c[j]=1;} }
  int T=omp_get_max_threads(); u32**tau=malloc(sizeof(void*)*T),**big=malloc(sizeof(void*)*T); u64**rem=malloc(sizeof(void*)*T);
  for(int t=0;t<T;t++){tau[t]=malloc(4*B);big[t]=malloc(4*B);rem[t]=malloc(8*(size_t)B);}
  u64 Tn=0,Pn=0,worst_n=0; long long worst=1LL<<60; int fail=0;
  for(u64 base=1; base<=X0; base+=(u64)T*B){
    #pragma omp parallel for schedule(static,1)
    for(int t=0;t<T;t++){ u64 lo=base+(u64)t*B; if(lo>X0) continue; u32*ta=tau[t],*bg=big[t]; u64*re=rem[t];
      for(int i=0;i<B;i++){re[i]=lo+i;ta[i]=1;bg[i]=1;}
      for(int i=0;i<np;i++){ u64 p=pr[i]; if(p*p>lo+B) break;
        for(u64 m=((lo+p-1)/p)*p; m<lo+B; m+=p){ int k=m-lo; u64 x=re[k]; u32 e=1; x/=p; while(x%p==0){x/=p;e++;} re[k]=x; ta[k]*=e+1; bg[k]=(u32)p; } }
      for(int i=0;i<B;i++) if(re[i]>1){ ta[i]*=2; bg[i]=(u32)re[i]; } }
    for(int t=0;t<T;t++){ u64 lo=base+(u64)t*B; if(lo>X0) break; u32*ta=tau[t],*bg=big[t];
      for(int i=0;i<B;i++){ u64 n=lo+i; if(n>X0) break; u32 tv=ta[i];
        if(n%tv==0) Tn++;
        if(tv==2) Pn++;
        long long mg=(long long)(2*Tn)-(long long)Pn; if(mg<0){ if(!fail) printf("COUNTEREXAMPLE: n=%llu pi=%llu T=%llu\n",(unsigned long long)n,(unsigned long long)Pn,(unsigned long long)Tn); fail=1; }
        if(n>=1000 && mg*1000 < (long long)Pn*0+worst*0+0){}                                   // (kept simple: track the smallest ratio below)
        if(n%(2*(u64)tv)==0 && n>1){ if(ngen==capgen){capgen=capgen?capgen*2:1<<20; gen_g=realloc(gen_g,4*capgen); gen_p=realloc(gen_p,4*capgen);} gen_g[ngen]=(u32)n; gen_p[ngen]=bg[i]; ngen++; } } } }
  printf("pointwise: pi(n) <= 2 T(n) for every n <= %llu: %s.  T(%llu) = %llu, pi(%llu) = %llu, ratio T/pi = %.5f.  generators g <= %llu: %zu\n",
    (unsigned long long)X0, fail?"FAILS":"holds",(unsigned long long)X0,(unsigned long long)Tn,(unsigned long long)X0,(unsigned long long)Pn,(double)Tn/Pn,(unsigned long long)X0,ngen); fflush(stdout);
  if(fail) return 1;
  // chain
  int K=0; u64*xs=malloc(8*100000); xs[K++]=X0; while(xs[K-1]<XMAX){ u64 nx=(u64)(xs[K-1]*RHO)+1; if(nx>XMAX)nx=XMAX; xs[K++]=nx; }
  u64*PI=calloc(K,8),*L=calloc(K,8);
  #pragma omp parallel for schedule(dynamic,1)
  for(int k=0;k<K;k++){ u64 x=xs[k]; u64 r=(u64)sqrtl((long double)x); while(r*r>x)r--; while((r+1)*(r+1)<=x)r++;
    u64*sm=malloc(8*(r+2)),*lg=malloc(8*(r+2)); lucy(x,r,sm,lg); PI[k]=lg[1]; u64 s=0;
    for(size_t j=0;j<ngen;j++){ u64 g=gen_g[j],p=gen_p[j]; if(p>r) continue; u64 y=x/g; if(y<=p) continue; u64 py = (g<=r)? lg[g] : sm[y]; s += py - sm[p]; }
    L[k]=s; free(sm); free(lg); }
  int ok=1; double minslack=1e9;
  for(int k=0;k<K;k++){ double slack = k+1<K ? (2.0*L[k])/PI[k+1] : 0;
    printf("x=%llu pi=%llu L=%llu L/pi=%.5f%s",(unsigned long long)xs[k],(unsigned long long)PI[k],(unsigned long long)L[k],(double)L[k]/PI[k], k+1<K?"":"\n");
    if(k+1<K){ int good = PI[k+1] <= 2*L[k]; printf("  step to %llu: 2L/pi(next) = %.5f %s\n",(unsigned long long)xs[k+1],slack,good?"ok":"FAIL"); if(!good)ok=0; if(slack<minslack)minslack=slack; } }
  printf("chain from %llu to %llu in %d steps: %s (smallest 2L(x_k)/pi(x_{k+1}) = %.5f)\n",(unsigned long long)xs[0],(unsigned long long)xs[K-1],K-1,ok?"every step holds":"SOME STEP FAILS",minslack);
  return !ok; }
