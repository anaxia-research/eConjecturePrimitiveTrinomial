from math import factorial, comb
from functools import lru_cache
def count(N, allowed):
    # number of perms sigma of [N] with sigma(i) in allowed[i]; DP over positions with bitmask of used values
    dp={0:1}
    for i in range(1,N+1):
        nd={}
        for mask,v in dp.items():
            for val in allowed[i]:
                b=1<<(val-1)
                if not mask&b: nd[mask|b]=nd.get(mask|b,0)+v
        dp=nd
    return sum(dp.values())
def allowed(n,j,first=None):
    N=2*n-1; A={}
    for i in range(1,N+1):
        s=set(range(1,N+1))
        if i%2==0: s={v for v in s if v<=i}
        elif i>=2*(n-j)+1: s={v for v in s if v>=i}
        if i==1 and first is not None: s=s&{first}
        A[i]=sorted(s)
    return N,A
def a(n,j): N,A=allowed(n,j); return count(N,A)
import sympy
xs=sympy.symbols('x')
G={1:sympy.Integer(1)}
for j in range(1,8): G[j+1]=sympy.expand((xs+1)*((xs+2)*G[j].subs(xs,xs+1)-xs*G[j]))
paper={1:[1,1],2:[4,2,2],3:[36,12,8,8],4:[576,144,72,56,56],5:[14400,2880,1152,720,608,608],6:[518400,86400,28800,14976,10656,9440,9440],7:[25401600,3628800,1036800,460800,281088,217152,198272,198272],8:[1625702400,203212800,50803200,19699200,10483200,7110144,5807232,5410688,5410688]}
for n in range(1,9):
    row=[a(n,j) for j in range(n+1)]
    assert row==paper[n],(n,row)
    for j in range(1,n+1):
        f=n-j
        assert row[j]==factorial(f)*factorial(f+1)*G[j].subs(xs,f)
    assert row[0]==factorial(n)**2
print("a(n,j) brute force == table == closed form, n<=8")
print([sympy.factor(G[j]) for j in range(2,7)])
print("G_j(0):",[G[j].subs(xs,0) for j in range(1,8)])
# (ii) recurrence
for n in range(1,8):
    for j in range(0,n+1):
        assert a(n+1,j+1)==a(n+1,j)-(n-j)*(n-j+1)*a(n,j)
print("(ii) verified n<=7")
# (iv)
for n in range(2,8):
    for j in range(1,n):
        for r in range(1,2*(n-j)+1):
            N,A=allowed(n,j,r); assert count(N,A)==-(-r//2)*a(n-1,j),(n,j,r)
    # j=0 all r
    for r in range(1,2*n):
        N,A=allowed(n,0,r); assert count(N,A)==-(-r//2)*factorial(n-1)**2
print("(iv) and j=0 first-letter formula verified n<=7")
# remark example n=3 j=2
print("D^r_{5,2}:",[count(*allowed(3,2,r)) for r in range(1,6)])
# upper-zone first letters r>2(n-j): data
for n in range(3,7):
    for j in range(1,n):
        print(n,j,[count(*allowed(n,j,r)) for r in range(1,2*n)])
