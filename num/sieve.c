// Extremes of the normalized prime-counting errors on [b_i, b_{i+1}], evaluated at every prime power (both one-sided limits).
// A=(x-psi)/sqrt x, B=(x-theta)/sqrt x, C=(li-Pi)*log x/sqrt x, D=(li-pi)*log x/sqrt x.   usage: sieve N < breakpoints
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdint.h>
typedef long double ld; typedef uint64_t u64;
typedef struct { u64 q; int k; double lp; } pw;
static int cmp(const void*a,const void*b){u64 x=((pw*)a)->q,y=((pw*)b)->q;return x<y?-1:x>y;}
static ld th=0,ps=0,Pi=0,li=0; static u64 pc=0; static double lastx=2;
static double mn[4],mx[4],amn[4],amx[4];
static void reset(void){for(int i=0;i<4;i++){mn[i]=1e300;mx[i]=-1e300;}}
static void adv(double x){ // advance li from lastx to x
  double a=lastx,gap=x-a; if(gap<=0)return; int n = a<1e5?64:(a<1e8?4:1); double h=gap/n; ld s=0;
  for(int i=0;i<n;i++){double c=a+h*(i+0.5),d=h*0.3872983346207417; s+=h*(5/log(c-d)+8/log(c)+5/log(c+d))/18;}
  li+=s; lastx=x; }
static void ev(double x){ double s=sqrt(x),L=log(x); double v[4]={(double)((x-ps)/s),(double)((x-th)/s),(double)((li-Pi)*L/s),(double)((li-(ld)pc)*L/s)};
  for(int i=0;i<4;i++){ if(v[i]<mn[i]){mn[i]=v[i];amn[i]=x;} if(v[i]>mx[i]){mx[i]=v[i];amx[i]=x;} } }
static void dump(double lo,double hi){ printf("%.17g %.17g",lo,hi); for(int i=0;i<4;i++)printf(" %.9f %.17g %.9f %.17g",mn[i],amn[i],mx[i],amx[i]);
  printf(" | theta=%.6Lf psi=%.6Lf pi=%llu li=%.6Lf\n",th,ps,(unsigned long long)pc,li); fflush(stdout); }
int main(int argc,char**argv){ u64 N=(u64)atof(argv[1]); u64 r=(u64)sqrtl((ld)N)+2;
  char*sm=calloc(r+1,1); u64*sp=malloc(sizeof(u64)*(r/2+10)); int ns=0;
  for(u64 i=2;i<=r;i++){ if(!sm[i]){sp[ns++]=i; for(u64 j=i*i;j<=r;j+=i)sm[j]=1;} }
  pw*P=malloc(sizeof(pw)*(ns*3+100)); int np=0;
  for(int i=0;i<ns;i++){u64 p=sp[i],q=p*p;int k=2; while(q<=N){P[np++]=(pw){q,k,log((double)p)}; if(q>N/p)break; q*=p;k++;}}
  qsort(P,np,sizeof(pw),cmp);
  double bp[4096];int nb=0; while(nb<4096&&scanf("%lf",&bp[nb])==1)nb++;
  int bi=0,pi_=0; reset(); li=1.045163780117492784844588889194613136L; // li(2)
  // before first breakpoint nothing is recorded; x starts at 2
  const u64 SEG=1<<20; unsigned char*seg=malloc(SEG); u64*nx=malloc(sizeof(u64)*ns);
  for(int i=1;i<ns;i++){u64 p=sp[i]; nx[i]=p*p;} // odd composites start
  #define CROSS(xq) while(bi<nb && bp[bi]<=(double)(xq)){ double b=bp[bi]; if(b<(double)(xq)||1){ adv(b); if(bi>0){ev(b);dump(bp[bi-1],b);} reset(); ev(b);} bi++; }
  #define EVENT(q,isprime,kk,lp) { CROSS(q) double x=(double)(q); adv(x); ev(x); if(isprime){th+=lp;ps+=lp;pc++;Pi+=1;} else {ps+=lp;Pi+=1.0L/(kk);} ev(x); }
  // prime 2
  { double l2=log(2.0); while(pi_<np&&P[pi_].q<2)pi_++; CROSS(2) th+=l2;ps+=l2;pc++;Pi+=1; ev(2.0); }
  for(u64 lo=3; lo<=N; lo+=2*SEG){ // seg[i] <-> lo+2i
    u64 hi=lo+2*SEG; if(hi>N+1)hi=N+1; memset(seg,0,SEG);
    for(int i=1;i<ns;i++){ u64 p=sp[i]; if(p*p>=hi)break; u64 j=nx[i]; if(j<lo){ j=((lo+p-1)/p)*p; if(!(j&1))j+=p; }
      for(;j<hi;j+=2*p)seg[(j-lo)>>1]=1; nx[i]=j; }
    for(u64 n=lo;n<hi;n+=2){ if(seg[(n-lo)>>1])continue;
      while(pi_<np&&P[pi_].q<n){ EVENT(P[pi_].q,0,P[pi_].k,P[pi_].lp) pi_++; }
      double lp=log((double)n); EVENT(n,1,1,lp) }
  }
  while(pi_<np&&P[pi_].q<=N){ EVENT(P[pi_].q,0,P[pi_].k,P[pi_].lp) pi_++; }
  CROSS(N+1)
  return 0; }
