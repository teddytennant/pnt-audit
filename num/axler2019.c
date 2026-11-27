// Axler, "New estimates for the n-th prime number", J. Integer Seq. 22 (2019), arXiv:1706.03651. From the LaTeX source.
// usage: axler2019 NMAX   (walks p_n and theta(p_n) for n <= NMAX)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef uint64_t u64;
#define SEG (1<<18)
static u64 lo=3; static int pos=0,ns=0,first=1; static unsigned char seg[SEG]; static u64*sp,*nx;
static void fill(void){ memset(seg,0,SEG); u64 hi=lo+2*(u64)SEG; for(int i=1;i<ns;i++){ u64 p=sp[i]; if(p*p>=hi)break; u64 j=nx[i]; if(j<lo){ j=((lo+p-1)/p)*p; if(!(j&1))j+=p; } for(;j<hi;j+=2*p)seg[(j-lo)>>1]=1; nx[i]=j; } pos=0; }
static u64 next(void){ if(first){first=0;return 2;} for(;;){ while(pos<SEG){ int i=pos++; if(!seg[i]) return lo+2*(u64)i; } lo+=2*(u64)SEG; fill(); } }
typedef struct { const char*name; u64 lo; double worst; u64 at; u64 nfail; u64 firstfail; } chk;
static chk C[]={ {"thm 1.1  p_n < n(ln n + lnln n - 1 + (lnln n - 2)/ln n - (lnln^2 n - 6 lnln n + 10.667)/(2 ln^2 n)), n>=46254381",46254381},
 {"thm 1.2  p_n > n(... 11.508 ...), n>=2",2}, {"lem 2.2  ln n >= 0.87 ln p_n, n>=1338564587",1338564587},
 {"prop 8.1 theta(p_n) > n(... 11.808 ...), n>=2",2}, {"prop 8.1 theta(p_n) < n(... 10.367 ...), n>=2581",2581} };
static void upd(int i,u64 n,double m){ if(n<C[i].lo)return; if(m<C[i].worst){C[i].worst=m;C[i].at=n;} if(m<0){ if(!C[i].nfail)C[i].firstfail=n; C[i].nfail++; } }
int main(int argc,char**argv){ u64 NMAX=(u64)atof(argv[1]); double lim=NMAX*(log((double)NMAX)+log(log((double)NMAX))+2)+1000; u64 r=(u64)sqrt(lim)+2;
  char*sm=calloc(r+1,1); sp=malloc(8*(r/2+10)); for(u64 i=2;i<=r;i++){ if(!sm[i]){sp[ns++]=i; for(u64 j=i*i;j<=r;j+=i)sm[j]=1;} } nx=malloc(8*ns); for(int i=0;i<ns;i++)nx[i]=sp[i]*sp[i]; fill();
  for(int i=0;i<5;i++)C[i].worst=1e300; long double th=0;
  for(u64 n=1;n<=NMAX;n++){ u64 p=next(); double lp=log((double)p); th+=lp; if(n<2) continue;
    double L=log((double)n), W=log(L), base=L+W-1+(W-2)/L; double q=W*W-6*W;
    upd(0,n,(double)n*(base-(q+10.667)/(2*L*L))-(double)p); upd(1,n,(double)p-(double)n*(base-(q+11.508)/(2*L*L)));
    upd(2,n,L-0.87*lp); upd(3,n,(double)th-(double)n*(base-(q+11.808)/(2*L*L))); upd(4,n,(double)n*(base-(q+10.367)/(2*L*L))-(double)th); }
  for(int i=0;i<5;i++){ printf("%s %s: worst %+.6g at n=%llu",C[i].nfail?"FAIL":"ok  ",C[i].name,C[i].worst,(unsigned long long)C[i].at); if(C[i].nfail)printf("; %llu failing n, first %llu",(unsigned long long)C[i].nfail,(unsigned long long)C[i].firstfail); printf("\n"); }
  printf("checked n <= %llu\n",(unsigned long long)NMAX); return 0; }
