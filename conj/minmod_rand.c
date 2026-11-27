// Random greedy search for a valid n-set mod N (see minmod.c): shuffle the residues, add each one that keeps the set valid.
// usage: minmod_rand n Nlo Nhi tries seed
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#define MAXN 20
#define MAXMOD 4200
static int valid(const int*a,int k,int N){
  static __thread unsigned char f[MAXN+1][MAXMOD], g[MAXN+1][MAXMOD];
  for(int c=0;c<=k;c++) memset(f[c],0,N); f[0][0]=1; int target=0; for(int i=0;i<k;i++) target=(target+a[i])%N;
  for(int i=0;i<k;i++){ for(int c=0;c<=k;c++) memset(g[c],0,N);
    for(int c=0;c<=k;c++) for(int r=0;r<N;r++){ unsigned char v=f[c][r]; if(!v)continue;
      int rr=r; for(int m=0;c+m<=k;m++){ unsigned char*p=&g[c+m][rr]; *p = (*p+v>2)?2:*p+v; rr+=a[i]; if(rr>=N)rr-=N; } }
    for(int c=0;c<=k;c++) memcpy(f[c],g[c],N); }
  return f[k][target]==1; }
int main(int argc,char**argv){ int n=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]); long tries=atol(argv[4]); unsigned seed=atoi(argv[5]);
  for(int N=hi;N>=lo;N--){ int best=0; int bestset[MAXN]; long hist[MAXN+1]; memset(hist,0,sizeof hist);
    #pragma omp parallel
    { unsigned s=seed*7919u+omp_get_thread_num()*104729u+N; int perm[MAXMOD],a[MAXN];
      #pragma omp for schedule(dynamic,16)
      for(long t=0;t<tries;t++){ for(int i=0;i<N-1;i++)perm[i]=i+1;
        for(int i=N-2;i>0;i--){ s=s*1103515245u+12345u; int j=(s>>8)%(i+1); int x=perm[i];perm[i]=perm[j];perm[j]=x; }
        int k=1; a[0]=0; for(int i=0;i<N-1&&k<n;i++){ a[k]=perm[i]; if(k<2||valid(a,k+1,N)) k++; }
        #pragma omp critical
        { hist[k]++; if(k>best){best=k; memcpy(bestset,a,sizeof(int)*k);} } } }
    printf("n=%d N=%d best=%d hist:",n,N,best); for(int k=2;k<=n;k++) if(hist[k]) printf(" %d:%ld",k,hist[k]);
    if(best==n){ printf("  VALID {"); for(int i=0;i<n;i++)printf("%d%s",bestset[i],i<n-1?",":"}"); } printf("\n"); fflush(stdout); }
  return 0; }
