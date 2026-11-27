// Fonollosa, arXiv:2607.08366, Conjecture 1: for N < 2^n - 2^floor(log2 n) no n-subset of Z/N is "valid".
// A is valid mod N when the only m : A -> N with sum m = |A| and sum m_a a = sum a (mod N) is m = 1.
// Validity is inherited by subsets and kept by a -> u a + c, so search sets containing 0 by DFS.
// usage: minmod n Nlo Nhi   -> prints, for each N, the number of valid n-sets containing 0 (stops counting at LIMIT) and one example
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 16
#define MAXMOD 4200
static int valid(const int*a,int k,int N){            // count solutions, saturating at 2
  static __thread unsigned char f[MAXN+1][MAXMOD], g[MAXN+1][MAXMOD];
  for(int c=0;c<=k;c++) memset(f[c],0,N); f[0][0]=1; int target=0; for(int i=0;i<k;i++) target=(target+a[i])%N;
  for(int i=0;i<k;i++){ for(int c=0;c<=k;c++) memset(g[c],0,N);
    for(int c=0;c<=k;c++) for(int r=0;r<N;r++){ unsigned char v=f[c][r]; if(!v)continue;
      int rr=r; for(int m=0;c+m<=k;m++){ unsigned char*p=&g[c+m][rr]; *p = (*p+v>2)?2:*p+v; rr+=a[i]; if(rr>=N)rr-=N; } }
    memcpy(f,g,sizeof(unsigned char)*(MAXN+1)*MAXMOD > 0 ? 0:0); for(int c=0;c<=k;c++) memcpy(f[c],g[c],N); }
  return f[k][target]==1; }
static long long found; static int ex[MAXN]; static long long LIMIT=1;
static void dfs(int*a,int k,int n,int N){ if(found>=LIMIT) return;
  if(k==n){
    #pragma omp critical
    { if(!found) memcpy(ex,a,sizeof(int)*n); found++; }
    return; }
  for(int x=a[k-1]+1; x<=N-(n-k); x++){ a[k]=x; if(k+1<3 || valid(a,k+1,N)) dfs(a,k+1,n,N); if(found>=LIMIT) return; } }
int main(int argc,char**argv){ int n=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]); if(argc>4) LIMIT=atoll(argv[4]);
  for(int N=hi;N>=lo;N--){ found=0;
    #pragma omp parallel for schedule(dynamic,1)
    for(int x=1;x<N;x++){ int a[MAXN]; a[0]=0; a[1]=x; if(found<LIMIT) dfs(a,2,n,N); }
    printf("n=%d N=%d valid sets found: %lld%s",n,N,found,found>=LIMIT?"+":""); if(found){ printf("  e.g. {"); for(int i=0;i<n;i++) printf("%d%s",ex[i],i<n-1?",":"}"); } printf("\n"); fflush(stdout); }
  return 0; }
