// Max clique (Tomita MCS-style with greedy colouring bound). Input on stdin:
// n mode target ; then n lines of 0/1 adjacency strings. mode 0: max size; mode 1: count cliques of size target (and report max).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#define MAXN 1100
#define W ((MAXN+63)/64)
typedef struct { uint64_t w[W]; } bs;
static int n, nw; static bs adj[MAXN];
static int best=0; static long long cnt=0; static int mode=0, target=0;
static long long nodes=0; static double tlimit=1e18; static clock_t t0; static int timedout=0;
static inline int pc(const bs*a){int s=0;for(int i=0;i<nw;i++)s+=__builtin_popcountll(a->w[i]);return s;}
static void expand(bs *P, int size){
  nodes++;
  if((nodes&0xFFFF)==0){ if((double)(clock()-t0)/CLOCKS_PER_SEC>tlimit){timedout=1;} }
  if(timedout) return;
  // colour classes
  int order[MAXN], col[MAXN], m=0; bs Q=*P; int c=0;
  while(1){ int any=0; for(int i=0;i<nw;i++) if(Q.w[i]) {any=1;break;} if(!any) break;
    c++; bs R=Q;
    while(1){ int v=-1; for(int i=0;i<nw;i++) if(R.w[i]){v=i*64+__builtin_ctzll(R.w[i]);break;} if(v<0)break;
      R.w[v>>6]&=~(1ULL<<(v&63)); Q.w[v>>6]&=~(1ULL<<(v&63));
      for(int i=0;i<nw;i++) R.w[i]&=~adj[v].w[i];
      order[m]=v; col[m]=c; m++; }
  }
  for(int k=m-1;k>=0;k--){
    int need = (mode==0)? best : target-1;
    if(size+col[k] <= need && !(mode==1 && size+col[k]>=target)) return;
    if(mode==0 && size+col[k]<=best) return;
    if(mode==1 && size+col[k]<target) return;
    int v=order[k]; bs NP; int any=0;
    for(int i=0;i<nw;i++){NP.w[i]=P->w[i]&adj[v].w[i]; if(NP.w[i])any=1;}
    if(!any){ if(size+1>best) best=size+1; if(mode==1 && size+1==target) cnt++; }
    else expand(&NP,size+1);
    P->w[v>>6]&=~(1ULL<<(v&63));
    if(timedout) return;
  }
}
int main(int argc,char**argv){
  if(argc>1) tlimit=atof(argv[1]);
  if(scanf("%d %d %d",&n,&mode,&target)!=3) return 1; nw=(n+63)/64;
  static char line[MAXN+5];
  for(int i=0;i<n;i++){ scanf("%s",line); memset(&adj[i],0,sizeof(bs)); for(int j=0;j<n;j++) if(line[j]=='1') adj[i].w[j>>6]|=1ULL<<(j&63); }
  bs P; memset(&P,0,sizeof P); for(int i=0;i<n;i++) P.w[i>>6]|=1ULL<<(i&63);
  t0=clock(); if(mode==1) best=0; expand(&P,0);
  printf("%d %lld %d %lld\n",best,cnt,timedout,nodes); return 0;
}
