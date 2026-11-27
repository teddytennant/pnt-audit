// Ramare & Zuniga Alterman, "From explicit estimates for the primes to explicit estimates for the Moebius function II", arXiv:2408.05969.
// M(X) = sum mu(n), m(X) = sum mu(n)/n, Q(X) = sum mu(n)^2, q(X) = sum mu(n)^2/n. All are constant on [n, n+1), so each bound is
// checked at X = n and as X -> (n+1)-.   usage: mobius N
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef struct { const char*name; double lo; double worst; double at; long nfail; double first; } chk;
static chk C[]={
 {"thm 1.1  |M(X)| <= (0.006688 ln X - 0.039) X/ln^2 X, X>=1798118",1798118},
 {"cor 1.2  |M(X)| <= (0.0130 ln X - 0.118) X/ln^2 X, X>=1078853",1078853},
 {"cor 1.3  |m(X)| <= (0.010032 ln X - 0.0568)/ln^2 X, X>=617990",617990},
 {"cor 1.4  |m(X)| <= (0.0144 ln X - 0.1)/ln^2 X, X>=463421",463421},
 {"lem 2.1  |Q(X) - 6X/pi^2| <= 0.02767 sqrt X, X>=438653",438653},
 {"lem 2.1  |Q(X) - 6X/pi^2| <= 0.7 sqrt X, X>=1",1},
 {"lem 2.2  |q(X) - (6/pi^2) ln X| <= 1.045, X>=1e6",1e6},
 {"lem 2.2  |q(X) - (6/pi^2) ln X| <= 1.48, X>=1",1},
 {"quoted in arXiv:2308.10084: |M(X)| <= X/4345, X>=2160535 (Cohen-Dress-El Marraki)",2160535},
 {"quoted in arXiv:2308.10084: |M(X)| <= X/80, X>=1119 (MacLeod)",1119},
};
#define NC (int)(sizeof(C)/sizeof(C[0]))
static int side_g;   // 1 while checking a left limit, which needs points of the domain below X
static void upd(int i,double X,double margin){ if(side_g ? X<=C[i].lo : X<C[i].lo) return; if(margin<C[i].worst){C[i].worst=margin;C[i].at=X;} if(margin<0){ if(!C[i].nfail)C[i].first=X; C[i].nfail++; } }
int main(int argc,char**argv){ long N=(long)atof(argv[1]); signed char*mu=malloc(N+2); memset(mu,1,N+2); char*comp=calloc(N+2,1);
  for(long p=2;p<=N;p++){ if(comp[p])continue; for(long m=p;m<=N;m+=p){ if(m>p)comp[m]=1; mu[m]=-mu[m]; } if(p*p<=N) for(long m=p*p;m<=N;m+=p*p) mu[m]=0; }
  for(int i=0;i<NC;i++){C[i].worst=1e300;}
  long M=0,Q=0; long double m=0,q=0; const double c6=6/(M_PI*M_PI);
  for(long n=1;n<=N;n++){ M+=mu[n]; m+=(long double)mu[n]/n; if(mu[n]){Q++; q+=1.0L/n;}
    for(int side=0;side<2;side++){ side_g=side; double X = side? (double)(n+1) : (double)n; if(side && n==N) break; double L=log(X);
      if(X>=463421){ double aM=fabs((double)M), am=fabsl(m);
        upd(0,X,(0.006688*L-0.039)*X/(L*L)-aM); upd(1,X,(0.0130*L-0.118)*X/(L*L)-aM);
        upd(2,X,(0.010032*L-0.0568)/(L*L)-am); upd(3,X,(0.0144*L-0.1)/(L*L)-am); }
      double dq=fabs((double)Q-c6*X); upd(4,X,0.02767*sqrt(X)-dq); upd(5,X,0.7*sqrt(X)-dq);
      { double aM2=fabs((double)M); upd(8,X,X/4345-aM2); upd(9,X,X/80-aM2); }
      if(X>1){ double dl=fabs((double)(q-(long double)c6*L)); upd(6,X,1.045-dl); upd(7,X,1.48-dl); } else { upd(7,X,1.48-fabs((double)q)); } } }
  for(int i=0;i<NC;i++){ printf("%s %-66s worst %+.6g at X=%.0f",C[i].nfail?"FAIL":"ok  ",C[i].name,C[i].worst,C[i].at); if(C[i].nfail) printf("; %ld failing points, first at X=%.0f",C[i].nfail,C[i].first); printf("\n"); }
  printf("checked integers n <= %ld (each at X = n and X -> n+1)\n",N); return 0; }
