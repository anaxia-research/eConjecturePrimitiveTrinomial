# V1: signed Eulerian polynomials. Exact checks.
import itertools, sys
from flint import fmpz_poly, fmpq_poly
from math import comb, factorial
import mpmath as mp

def eulerian(n):
    # A_n(t) coefficients: A(n,k) via recurrence
    A=[1]
    for m in range(2,n+1):
        B=[0]*m
        for k in range(m):
            a = A[k] if k < len(A) else 0
            b = A[k-1] if k-1>=0 and k-1 < len(A) else 0
            B[k]=(k+1)*a+(m-k)*b
        A=B
    return A
def P(c): return fmpz_poly(c)
def sign(p):
    s=1; p=list(p); seen=[False]*len(p)
    for i in range(len(p)):
        if not seen[i]:
            j=i; L=0
            while not seen[j]: seen[j]=True; j=p[j]; L+=1
            if L%2==0: s=-s
    return s
# brute force identities n<=8
t=fmpz_poly([0,1]); one=fmpz_poly([1])
for n in range(1,9):
    Ap=[0]*n; Am=[0]*n; Ep=[0]*n; Em=[0]*n
    for p in itertools.permutations(range(n)):
        d=sum(1 for i in range(n-1) if p[i]>p[i+1]); e=sum(1 for i in range(n) if p[i]>i)
        if sign(p)==1: Ap[d]+=1; Ep[e]+=1
        else: Am[d]+=1; Em[e]+=1
    An=P(eulerian(n))
    m=(n+1)//2
    lhsA=P(Ap)-P(Am); rhsA=(one-t)**(n//2)*P(eulerian(m))
    lhsE=P(Ep)-P(Em); rhsE=(one-t)**(n-1)
    assert lhsA==rhsA, n; assert lhsE==rhsE, n
    assert P(Ap)+P(Am)==An and P(Ep)+P(Em)==An
print("identities (Mantaci, Desarmenien-Foata) verified by brute force n<=8")
def signed(n):
    An=P(eulerian(n)); m=(n+1)//2
    dA=(one-t)**(n//2)*P(eulerian(m)); dE=(one-t)**(n-1)
    return {'A+':(An+dA), 'A-':(An-dA), 'E+':(An+dE), 'E-':(An-dE)}  # these are 2x the polys
E5p=signed(5)['E+']; print("2E5+ =",E5p, " real roots:", sum(1 for r in E5p.complex_roots() if abs(r[0].imag)<1e-30))
# exact real root counting: use fmpz_poly.complex_roots (rigorous arb isolation) and also sympy sturm for cross-check on subset
import sympy
x=sympy.symbols('x')
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 60
bad=[]
for n in range(2,NMAX+1):
    for key,poly in signed(n).items():
        c=[int(v) for v in poly.coeffs()]
        # strip zero top
        while c and c[-1]==0: c.pop()
        deg=len(c)-1
        sp=sympy.Poly(list(reversed(c)),x)
        nreal=sp.count_roots()   # exact (Sturm / Vincent-type) with multiplicity
        sq=sympy.Poly(sympy.gcd(sp, sp.diff(x)),x)
        if nreal!=deg: bad.append((n,key,deg,nreal))
        if n>=6 and sq.degree()>0 and not (key=='E-' ): pass
print("polys with nonreal zeros (n,key,deg,#real):", bad)
