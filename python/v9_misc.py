import itertools, math
from math import comb
exec(open(__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/v6b_cliques.py').read().split("if __name__")[0])
exec(open(__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/v7_sigma.py').read().split("for n in range(2,9)")[0])
# 7x7 odd family
W="""01001101101010 01111001100010 01111100110000 00000011011111 01010001111010 00001101010111 00000001111111 01111100100100 11111001000001 11011001100001 00000011110111 00000110111011 10100011010101 00011011110100 00000110101111 01001100111010 01111001101000 01111011100000 11110001100001 10100110100101 11101100100001 01101000101011 01100110001011""".split()
F=[tuple(int(c) for c in w) for w in W]
assert len(set(F))==23 and all(sum(w)==7 and len(w)==14 for w in F)
assert all(common2(x,y)%2==1 for x,y in itertools.combinations(F,2)); print("7x7 odd family of 23: OK")
# three rows family T_a (even family to (a,3)) and two-row families
def word(a,cols):  # path from abscissas of north steps
    w=[];cur=0
    for c in cols: w+= [0]*(c-cur)+[1]; cur=c
    return tuple(w+[0]*(a-cur))
def Ta(a):
    S=set()
    for z in range(1,a,2): S.add(word(a,(0,1,z))); S.add(word(a,(z,a-1,a)))
    for z in range(4,a-1,2): S.add(word(a,(2,3,z)))
    for z in range(2,a-3,2): S.add(word(a,(z,a-3,a-2)))
    S.add(word(a,(0,0,0))); S.add(word(a,(a,a,a))); return S
for a in range(4,41,2):
    T=Ta(a); assert len(T)==(9 if a==6 else 2*a-2) and all(common2(x,y)%2==0 for x,y in itertools.combinations(T,2)),a
print("T_a even families verified a<=40")
def two_M(a):
    e=2*(a//2); S={word(a,(k,k)) for k in range(0,a+1,2)}|{word(a,(0,1)),word(a,(e-1,e))}; return S
def two_Ms(a):
    if a%2==1:
        S={word(a,(2*j,2*j+1)) for j in range(0,(a-3)//2+1)}|{word(a,(4*t,4*t+3)) for t in range(0,(a-5)//4+1) if 4*t<=a-5}|{word(a,(o,a)) for o in range(1,a+1,2)}
        return S
    b=a-1; S={word(a,(2*j+1,2*j+2)) for j in range(0,(b-3)//2+1)}|{word(a,(4*t+1,4*t+4)) for t in range(0,(b-5)//4+1) if 4*t<=b-5}|{word(a,(o+1,a)) for o in range(1,b+1,2)}|{word(a,(0,a))}
    return S
for a in range(2,41):
    S=two_M(a); m=a+2
    assert len(S)==a//2+3 and all(common2(x,y)%2==m%2 for x,y in itertools.combinations(S,2)),a
    if a>=2:
        S2=two_Ms(a); target=(5*a-1)//4 if a%2 else (5*a-2)//4
        assert len(S2)==target and all(common2(x,y)%2==(m+1)%2 for x,y in itertools.combinations(S2,2)),(a,len(S2),target)
print("two-row constructions verified 2<=a<=40")
# window construction for even n<=30 using T_{n-2} reflected (width 3 windows) and width-1 window
def refl(w): return tuple(1-c for c in w)
def window_family(n):
    fam=[]; j=0
    ws=[3]*(n//4) if n%4==0 else [3]*((n-2)//4)+[1]
    for w in ws:
        if w==3: G=[refl(t) for t in Ta(n-2)]   # paths to (3,n-2)
        else: G=[tuple([1]*k+[0]+[1]*(n-2-k)) for k in range(0,n-1,2)]
        for tau in G: fam.append(tuple([0]*j+[1]+list(tau)+[1]+[0]*(n-w-j)))
        j+=w+1
    return fam
for n in range(10,31,2):
    if n in (10,12,14,16,18,20,22,24,26,28,30):
        F=window_family(n); assert len(set(F))==len(F) and all(sum(f)==n for f in F)
        assert all(common2(x,y)%2==1 for x,y in itertools.combinations(F,2)),n
        exp= n*n//2-3*n//2 if n%4==0 else n*n//2-2*n+3
        assert len(F)==exp,(n,len(F),exp)
print("window families (Thm oddsq-half) verified for even 10<=n<=30")
# meander table, det G_n
import sympy
for n in range(1,7):
    Ms=list(ncpm(n)); cnt={}
    def comps(M1,M2):
        par=list(range(2*n+1))
        def f(x):
            while par[x]!=x: par[x]=par[par[x]]; x=par[x]
            return x
        for a,b in M1+M2: par[f(a)]=f(b)
        return len({f(x) for x in range(1,2*n+1)})
    G=[[2**comps(M1,M2) for M2 in Ms] for M1 in Ms]
    for row,M1 in zip(G,Ms):
        for v in row: c=int(math.log2(v)); cnt[c]=cnt.get(c,0)+1
    print(n,[cnt.get(c,0) for c in range(1,n+1)], "det" if n<=4 else "", sympy.Matrix(G).det() if n<=4 else "")
