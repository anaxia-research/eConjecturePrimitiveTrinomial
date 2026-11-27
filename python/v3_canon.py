import sys, itertools
from math import comb, factorial
from fractions import Fraction as Fr
from flint import fmpz_poly, fmpz_mat, fmpq
def C(n,k): return comb(n,k) if 0<=k<=n else 0
# ---- direct DP over lattice words on 3 letters with pattern state, descent polynomial via Kronecker ints
def dp(k, avoid, B=None):
    # avoid in {'231','321'}; returns list of coefficients of descent polynomial
    # state: (n1,n2,n3,last,flag) ; flag tracks pattern progress
    # 321: flag0 no 3 yet; flag1 a 3 seen; flag2 a 2 after a 3 seen (then 1 forbidden)
    # 231: avoid iff last 1 precedes first 3 (Shankar Thm 3.2) -- we track directly: flag0 nothing; flag1 a 2 seen; flag2 a 3 after a 2 seen (then 1 forbidden)
    if B is None: B=3*k+8
    from collections import defaultdict
    cur={(1,0,0,1,0):1}
    for pos in range(1,3*k):
        nxt=defaultdict(int)
        for (a,b,c,last,fl),v in cur.items():
            for L in (1,2,3):
                na,nb,nc=a+(L==1),b+(L==2),c+(L==3)
                if na>k or nb>na or nc>nb: continue
                if avoid=='321':
                    if L==1 and fl==2: continue
                    nf=fl
                    if L==3 and fl==0: nf=1
                    if L==2 and fl==1: nf=2
                else:
                    if L==1 and fl==2: continue
                    nf=fl
                    if L==2 and fl==0: nf=1
                    if L==3 and fl==1: nf=2
                w=v<<B if L<last else v
                nxt[(na,nb,nc,L,nf)]+=w
        cur=nxt
    tot=sum(cur.values())
    out=[]; mask=(1<<B)-1
    while tot: out.append(tot&mask); tot>>=B
    return out
def brute(k,pat):
    # brute force for small k : enumerate lattice words
    res=[0]*(3*k)
    def contains(w,p):
        idx={1:p[0],2:p[1],3:p[2]}
        # pattern p as permutation of (1,2,3): occurrence = subsequence order-isomorphic; letters distinct values -> must use letters 1,2,3 in order given by p
        target=[int(ch) for ch in p]
        j=0
        for ch in w:
            if ch==target[j]:
                j+=1
                if j==3: return True
        return False
    def rec(w,a,b,c):
        if len(w)==3*k:
            if not contains(w,pat):
                d=sum(1 for i in range(len(w)-1) if w[i]>w[i+1]); res[d]+=1
            return
        if a<k: rec(w+[1],a+1,b,c)
        if b<a: rec(w+[2],a,b+1,c)
        if c<b: rec(w+[3],a,b,c+1)
    rec([],0,0,0)
    while res and res[-1]==0: res.pop()
    return res
for k in range(1,6):
    assert dp(k,'231')==brute(k,'231'), k
    assert dp(k,'321')==brute(k,'321'), k
print("DP == brute force for k<=5; B3=",dp(3,'231')," Q3=",dp(3,'321'))
def Bclosed(k,m):
    q=(k*k-k+4)*m*m+(3*k*k-13*k+2)*m+8*k*k-4*k
    return Fr(C(2*k,m)*C(k,m)*q, 2*k*(2*k-1)*(m+1)*(m+2))
for k in range(2,41):
    co=dp(k,'231')
    assert [Fr(x) for x in co]==[Bclosed(k,m) for m in range(len(co))] and all(Bclosed(k,m)==0 for m in range(len(co),k+1)), k
print("closed form (canon-closed) verified 2<=k<=40")
# Jacobi expansion
X=fmpz_poly([0,1])
def pn(n,k): return [C(n+k,m)*C(n+2,n-m) for m in range(n+1)]
from flint import fmpq_poly
for k in range(2,41):
    c0=Fr(k*k+k+2,(3*k+1)*(3*k+2)); c1=Fr(2*(k-2)*(k+2),3*k*(3*k+2)); c2=Fr(k*k-k+4,3*k*(3*k+1))
    xm1=fmpq_poly([-1,1])
    rhs=fmpq_poly(pn(k,k))*fmpq(c0.numerator,c0.denominator)+fmpq(c1.numerator,c1.denominator)*xm1*fmpq_poly(pn(k-1,k))+fmpq(c2.numerator,c2.denominator)*xm1**2*fmpq_poly(pn(k-2,k))
    assert rhs==fmpq_poly(dp(k,'231')), k
print("Jacobi expansion verified 2<=k<=40")
# real-rootedness of B_k: sympy count_roots for k<=60 using closed form
import sympy
x=sympy.symbols('x')
for k in range(1,61):
    co=[Bclosed(k,m) if k>=2 else Fr(1) for m in range(k+1)] if k>=2 else [Fr(1)]
    den=1
    for v in co: den=den*v.denominator//__import__('math').gcd(den,v.denominator)
    ci=[int(v*den) for v in co]
    while ci[-1]==0: ci.pop()
    p=sympy.Poly(ci[::-1],x)
    if k>=3: assert p.count_roots(None,0)==len(ci)-1, k
print("B_k: deg distinct negative real roots for 3<=k<=60")
