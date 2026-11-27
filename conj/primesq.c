// OEIS A105720: a(n) = p_n + p_{n+1} + ... + p_{2n}. Conjectured to be a square only for n = 3, 6, 4072.  usage: primesq NMAX
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
#define SEG (1<<18)
typedef struct { u64 lo; int pos; unsigned char*seg; u64*sp; u64*nx; int ns; u64 limit; int first; } gen;
static void fill(gen*g){ memset(g->seg,0,SEG); u64 hi=g->lo+2*(u64)SEG;
  for(int i=1;i<g->ns;i++){ u64 p=g->sp[i]; if(p*p>=hi)break; u64 j=g->nx[i]; if(j<g->lo){ j=((g->lo+p-1)/p)*p; if(!(j&1))j+=p; } for(;j<hi;j+=2*p)g->seg[(j-g->lo)>>1]=1; g->nx[i]=j; } g->pos=0; }
static gen*mk(u64 limit){ gen*g=calloc(1,sizeof(gen)); u64 r=(u64)sqrtl((long double)limit)+2; char*sm=calloc(r+1,1); g->sp=malloc(8*(r/2+10));
  for(u64 i=2;i<=r;i++){ if(!sm[i]){g->sp[g->ns++]=i; for(u64 j=i*i;j<=r;j+=i)sm[j]=1;} }
  g->nx=malloc(8*g->ns); for(int i=0;i<g->ns;i++)g->nx[i]=g->sp[i]*g->sp[i]; g->seg=malloc(SEG); g->lo=3; g->first=1; fill(g); return g; }
static u64 next(gen*g){ if(g->first){g->first=0;return 2;} for(;;){ while(g->pos<SEG){ int i=g->pos++; if(!g->seg[i]) return g->lo+2*(u64)i; } g->lo+=2*(u64)SEG; fill(g); } }
int main(int argc,char**argv){ u64 NMAX=(u64)atof(argv[1]); double lim=2.0*NMAX*(log(2.0*NMAX)+log(log(2.0*NMAX))+2)+1000;
  gen*hi=mk((u64)lim),*lo=mk((u64)lim);
  // a(1) = p1 + p2.  a(n+1) = a(n) - p_n + p_{2n+1} + p_{2n+2}
  u128 a=(u128)next(hi)+next(hi); u64 found=0;
  for(u64 n=1;n<=NMAX;n++){ long double x=sqrtl((long double)a); u64 rt=(u64)x; while((u128)rt*rt>a)rt--; while((u128)(rt+1)*(rt+1)<=a)rt++;
    if((u128)rt*rt==a){ printf("square at n = %llu: a(n) = %llu^2\n",(unsigned long long)n,(unsigned long long)rt); fflush(stdout); found++; }
    a-=next(lo); a+=next(hi); a+=next(hi); }
  printf("searched n <= %llu, squares found: %llu\n",(unsigned long long)NMAX,(unsigned long long)found); return 0; }
