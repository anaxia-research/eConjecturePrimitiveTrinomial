// enumerate permutations of [n] with c(pi) <= T by backtracking; count, orbits (canonical under 8 symmetries), n-cycles
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n,T; static int p[32], used[33]; static long long cnt=0, cyc=0, orb=0;
static int cval(int *q,int i,int j){ int lo=q[i]<q[j]?q[i]:q[j], hi=q[i]<q[j]?q[j]:q[i], c=0; for(int k=i;k<=j;k++) if(q[k]>=lo&&q[k]<=hi) c++; return c; }
static int ccheck(int *q){int m=0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){int c=cval(q,i,j); if(c>m)m=c;} return m;}
static int iscycle(int *q){ int seen[32]={0},x=0,L=0; while(!seen[x]){seen[x]=1;x=q[x]-1;L++;} return L==n; }
static void sym(int *q,int s,int *r){ // apply symmetry s of square to diagram
  int t[32];
  for(int i=0;i<n;i++){ int x=i+1,y=q[i],X,Y;
    switch(s&3){case 0:X=x;Y=y;break; case 1:X=y;Y=n+1-x;break; case 2:X=n+1-x;Y=n+1-y;break; default:X=n+1-y;Y=x;}
    if(s&4){ X=n+1-X; }
    t[X-1]=Y; }
  memcpy(r,t,sizeof(int)*n);
}
static int lexless(int*a,int*b){for(int i=0;i<n;i++){if(a[i]!=b[i])return a[i]<b[i];}return 0;}
static void rec(int pos){
  if(pos==n){ cnt++; if(iscycle(p)) cyc++;
    int canon=1, r[32]; for(int s=1;s<8;s++){ sym(p,s,r); if(lexless(r,p)){canon=0;break;} } if(canon) orb++;
    if(n==9||n==14){ for(int i=0;i<n;i++) printf("%d ",p[i]); printf(" c=%d\n",ccheck(p)); }
    return; }
  for(int v=1;v<=n;v++) if(!used[v]){
    p[pos]=v; int ok=1;
    for(int i=0;i<pos && ok;i++){ if(cval(p,i,pos)>T) ok=0; }
    if(ok){ used[v]=1; rec(pos+1); used[v]=0; }
  }
}
int main(int argc,char**argv){ n=atoi(argv[1]); T=atoi(argv[2]); rec(0); printf("n=%d T=%d count=%lld orbits=%lld cycles=%lld\n",n,T,cnt,orb,cyc); return 0;}
