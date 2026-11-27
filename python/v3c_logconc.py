import sys
exec(open(__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/v3_canon.py').read().split('def brute')[0])
import sympy
x=sympy.symbols('x')
KMAX=int(sys.argv[1]); RMAX=int(sys.argv[2])
fail=[]; nonreal={}
for k in range(1,KMAX+1):
    c=dp(k,'321')
    for i in range(1,len(c)-1):
        if c[i]*c[i]<c[i-1]*c[i+1]: fail.append((k,i))
    assert all(v>0 for v in c)
    if k<=RMAX:
        p=sympy.Poly(c[::-1],x); nr=len(c)-1-p.count_roots()
        nonreal[k]=nr
    print(k,len(c)-1,nonreal.get(k),flush=True)
print("log-concavity failures:",fail)
print("nonreal zero counts:",nonreal)
