import itertools, mpmath as mp
exec(open(__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/v6b_cliques.py').read().split("if __name__")[0])
# B_k moments
mp.mp.dps=30
def w_of_phi(phi):
    c=mp.cos(phi); x=mp.sin(3*phi)**3/(mp.sin(phi)*mp.sin(2*phi)**2)
    w=(4*c**2-1)*(64*c**6-112*c**4+44*c**2+7)/(8*c*mp.sin(phi)*(8*c**2+1))/(mp.pi*x)
    return x,w
def moment(k):
    # integral over x in (0,27/4) of x^k w(x) dx = integral over phi of x^k w(x) |dx/dphi| dphi
    f=lambda phi: (lambda xw: xw[0]**k*xw[1]*abs(mp.diff(lambda p: mp.sin(3*p)**3/(mp.sin(p)*mp.sin(2*p)**2),phi)))(w_of_phi(phi))
    return mp.quad(f,[0,mp.pi/6,mp.pi/3])
B=[1,1,4,21,121,728,4488]
print("B_k moments:",[mp.nstr(moment(k),12) for k in range(7)],"expected",B)
# caged
def cval(p):
    n=len(p); best=0
    for i in range(n):
        for j in range(i+1,n):
            lo,hi=min(p[i],p[j]),max(p[i],p[j]); best=max(best,sum(1 for k in range(i,j+1) if lo<=p[k]<=hi))
    return best
def iscyc(p):
    x=0;L=0;seen=set()
    while x not in seen: seen.add(x); x=p[x]-1; L+=1
    return L==len(p)
cyc={5:"2 3 5 1 4",6:"2 3 6 5 1 4",7:"2 5 7 1 6 3 4",8:"3 6 2 8 1 7 4 5",10:"2 6 9 10 1 7 8 3 4 5",11:"3 7 2 10 11 1 8 9 4 5 6",12:"4 3 8 2 11 12 1 9 10 5 6 7",13:"5 4 9 3 12 13 6 11 1 2 10 7 8",15:"4 3 9 2 10 14 15 1 11 13 12 5 6 7 8",16:"5 4 10 3 2 11 15 16 1 12 14 13 6 7 8 9"}
for n,w in cyc.items():
    p=list(map(int,w.split())); assert sorted(p)==list(range(1,n+1)) and iscyc(p) and cval(p)==n//5+2,(n,cval(p))
print("ten explicit cycles OK")
def construct(n):
    K=n//5+1; m=n-4*K; assert 0<=m<=K-1 and K>=2
    beta=[0]*(n+1)
    for p in range(1,K+1): beta[p]=2*K+m+p
    for q in range(1,K+1): beta[K+q]=K+1-q
    for t in range(1,K+1): beta[2*K+m+t]=n+1-t
    for u in range(1,K+1): beta[3*K+m+u]=K+u
    for i in range(1,m+1): beta[2*K+i]=2*K+i+1 if i<m else 2*K+1
    tau={}
    def sw(a,b): tau[a]=b; tau[b]=a
    for q in range(1,K):
        if q%2==1: sw(2*K+m+q,2*K+m+q+1)
        else: sw(n-q,n+1-q)
    if m>=1: sw(2*K,2*K+1)
    pi=[tau.get(beta[i],beta[i]) for i in range(1,n+1)]
    return pi
for n in range(8,61):
    if n in (10,11,15): continue
    p=construct(n); assert sorted(p)==list(range(1,n+1)) and iscyc(p) and cval(p)<=n//5+3,(n,cval(p))
print("general n-cycle construction OK for 8<=n<=60 (n!=10,11,15); n=9 example:",construct(9))
# (2,2,2) family and (1,1,1,1) family
fam="001221 002121 012201 020211 022011 100122 101022 110202 112002 120012 201120 212010 212100 221010 221100".split()
F=[tuple(map(int,w)) for w in fam]; assert all(common(x,y)%2==0 for x,y in itertools.combinations(F,2)) and len(set(F))==15
fam4="0132 0312 1023 1203 2301 2310 3201 3210".split(); F4=[tuple(map(int,w)) for w in fam4]
assert all(common(x,y)%2==0 for x,y in itertools.combinations(F4,2)); print("(2,2,2) and (1,1,1,1) families OK")
