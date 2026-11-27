import itertools, math
from math import comb, gcd
def rank2(rows):
    # rows as ints (bitmasks); GF(2) rank
    basis=[]; 
    for r in rows:
        for b in basis: r=min(r,r^b)
        if r: basis.append(r)
    return len(basis), basis
def grid(a,b):
    idx=lambda i,j:(i-1)+a*(j-1)
    rows=[]
    for j in range(1,b+1):
        for i in range(1,a+1):
            r=0
            for (p,q) in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
                if 1<=p<=a and 1<=q<=b: r|=1<<idx(p,q)
            rows.append(r)
    return rows
for a in range(1,25):
    for b in range(1,25):
        r,_=rank2(grid(a,b)); assert r==a*b-gcd(a+1,b+1)+1,(a,b)
print("grid rank formula verified 1<=a,b<=24")
# tau in column space, a+b even, a,b<=10
def in_colspace(a,b):
    rows=grid(a,b); n=a*b
    tau=0
    for j in range(1,b+1):
        for i in range(1,a+1):
            if ((i==1)+(j==b))%2: tau|=1<<((i-1)+a*(j-1))
    r1,_=rank2(rows); r2,_=rank2(rows+[tau])   # symmetric matrix: column space = row space
    return r1==r2
res=[]
for a in range(1,11):
    for b in range(1,11):
        if (a+b)%2==0:
            pred=(a%2==0 and b%2==0) or a==b or (a%2==1 and b%2==1 and a%4==1 and b%4==1)
            if in_colspace(a,b)!=pred: res.append((a,b,in_colspace(a,b)))
print("tau column-space rule exceptions (a,b<=10):",res)
# skeletons count, ballot numbers, a_m, depth formula
def skeletons(m):
    out=[]
    for eps in itertools.product((1,-1),repeat=m):
        s=0; ok=True
        for e in eps:
            s+=e
            if s<0: ok=False;break
        if ok: out.append(eps)
    return out
for m in range(0,15):
    sk=skeletons(m); assert len(sk)==comb(m,m//2)
    for j in range(0,m//2+1):
        assert sum(1 for e in sk if e.count(-1)==j)==comb(m,j)-(comb(m,j-1) if j>=1 else 0)
print("skeleton (ballot) counts verified m<=14")
# total classes a_m = sum 2^k
am=[sum(2**(m-2*e.count(-1)) for e in skeletons(m)) for m in range(8)]; print("a_m:",am)
# depth: S_h(m)
def depth_count(m,h):
    c=0
    for e in skeletons(m):
        # depth = max open arcs: arcs open = (#up steps that are left ends) ... compute via matching
        stack=[];free=[];mx=0;opened=0
        # match each -1 with nearest unmatched +1 to left; free points = unmatched +1
        st=[]
        pairs=[]
        for i,x in enumerate(e):
            if x==1: st.append(i)
            else: pairs.append((st.pop(),i))
        L=[0]*(m+1)
        for (p,q) in pairs:
            for t in range(p,q): L[t]+=1
        d=max(L) if m else 0
        if d<=h: c+=1
    return c
print("S2:",[depth_count(m,2) for m in range(11)])
for h in range(0,4):
    for m in range(0,13):
        f=4/(2*h+3)*sum(math.cos(i*math.pi/(2*(2*h+3)))**2*(2*math.cos(i*math.pi/(2*h+3)))**m for i in range(1,2*h+2,2))
        assert round(f)==depth_count(m,h) and abs(f-round(f))<1e-6,(h,m)
print("depth formula verified h<=3, m<=12")
