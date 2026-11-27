from flint import fmpz_mat, fmpz_poly
def D(n):
    S=[('e',i) for i in range(1,n)]+[('f',j) for j in range(1,n-1)]
    def st(s): return (s[1],s[1]+1) if s[0]=='e' else (s[1],s[1]+2)
    m=len(S); M=[[0]*m for _ in range(m)]
    for a in range(m):
        for b in range(m):
            u=st(S[a])+st(S[b]); M[a][b]=max(u)-min(u)
    return M
res={}
for n in range(3,61):
    M=D(n); cp=fmpz_mat(M).charpoly(); c=[int(x) for x in cp.coeffs()]
    m=2*n-3; assert len(c)==m+1 and c[m]==1
    a2=c[2*n-5]; formula=-(n-1)*(n-2)*(2*n*n+6*n-15)//6
    assert a2==formula,(n,a2,formula)
    assert abs(c[0])==n-1 and abs(c[1])==4*n*n-14*n+13 and abs(c[2*n-4])==3*n-5
    absv=[abs(x) for x in c[:2*n-3]]   # |a_0|..|a_{2n-4}|
    mx=max(absv); idx=[i for i,v in enumerate(absv) if v==mx]
    res[n]=idx
    if n in (15,16): print(n,[absv[i] for i in range(n-2,n+3)])
print("a_{2n-5} formula, |a0|,|a1|,|a_{2n-4}| verified for 3<=n<=60")
print({n:(res[n][0]-(n-1)) for n in res})
assert all(len(v)==1 for v in res.values())
import sympy
# second independent method for n=15,16: sympy charpoly
for n in (15,16):
    cp=sympy.Matrix(D(n)).charpoly().all_coeffs()[::-1]
    assert [int(v) for v in cp]==[int(x) for x in fmpz_mat(D(n)).charpoly().coeffs()]
print("n=15,16 cross-checked with sympy")
