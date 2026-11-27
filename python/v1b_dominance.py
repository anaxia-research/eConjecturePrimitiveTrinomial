# numerical check of the dominance lemma at the test points, all m in [1, ceil(n/2)], n=50..NMAX
import mpmath as mp, sys
mp.mp.dps=60
def eul(n):
    A=[1]
    for m in range(2,n+1):
        B=[0]*m
        for k in range(m):
            a=A[k] if k<len(A) else 0; b=A[k-1] if 0<=k-1<len(A) else 0
            B[k]=(k+1)*a+(m-k)*b
        A=B
    return A
EU={}
def Lder(n,s):
    # L^{(n)}(s) = (-1)^n t A_n(t)/(1-t)^{n+1}, t=-e^{-s}
    if n not in EU: EU[n]=eul(n)
    t=-mp.e**(-s); A=sum(c*t**i for i,c in enumerate(EU[n]))
    return (-1)**n*t*A/(1-t)**(n+1)
worst=mp.inf
for n in range(50,int(sys.argv[1])+1):
    K=int(mp.floor(mp.sqrt(n)/2))
    pts={}
    for i in range(2,(n+1)//2+1):
        pts[i]= mp.mpf(n)/i if i<=K else mp.pi*mp.cot(i*mp.pi/(n+1))
    for i in list(pts): pts[n+1-i]=-pts[i]
    for i in range(2,n):
        s=pts[i]; lhs=(-1)**(n+i)*Lder(n,s)
        assert lhs>0
        for m in range(1,(n+1)//2+1):
            r=abs(Lder(m,s))/lhs
            if r>=1: print("FAIL",n,i,m,r)
            worst=min(worst,1-r) if False else worst
            if r> (0 if worst==mp.inf else 0): pass
        mx=max(abs(Lder(m,s)) for m in range(1,(n+1)//2+1))/lhs
        if worst==mp.inf or mx>worst: worst=mx; arg=(n,i)
    print(n,"max ratio |L^(m)|/((-1)^{n+i}L^(n)) over i,m so far:",mp.nstr(worst,6),arg,flush=True)
