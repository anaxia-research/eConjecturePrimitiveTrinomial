import itertools, sys
sys.argv_save=sys.argv; sys.argv=['x','none']
exec(open(__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/v6b_cliques.py').read().split("if __name__")[0])
from math import prod
def boxpaths(p):
    letters=[c for c,k in enumerate(p) for _ in range(k)]
    return sorted(set(itertools.permutations(letters)))
def rankF2(M):
    rows=[int(''.join(map(str,r)),2) for r in M]; basis=[]
    for r in rows:
        for b in basis: r=min(r,r^b)
        if r: basis.append(r)
    return len(basis)
paper={(1,1):(2,1,0,2),(2,2):(4,2,2,5),(3,3):(8,3,6,10),(4,2):(5,4,8,9),(5,1):(2,3,4,6),(6,2):(6,7,12,13),
(1,1,1):(2,3,4,6),(2,1,1):(5,3,8,10),(2,2,1):(5,7,14,17),(3,1,1):(5,6,12,14),(2,2,2):(15,7,22,29),(3,2,1):(12,7,24,24),(4,1,1):(7,6,16,18),
(3,3,1):(12,13,28,34),(3,2,2):(15,16,38,41),(4,2,1):(12,11,31,31),(5,1,1):(7,9,20,22),(4,2,2):(30,16,50,53),(3,3,2):(37,16,54,58),(4,3,1):(26,13,44,44),
(1,1,1,1):(8,3,12,18),(2,1,1,1):(8,10,28,30),(2,2,1,1):(24,10,42,50),(3,1,1,1):(14,10,36,42),(1,1,1,1,1):(8,15,36,50),(2,1,1,1,1):(31,15,76,82)}
for p,(madm,moth,R,EV) in paper.items():
    V=boxpaths(p); m=sum(p)
    Bm=[[common(x,y)%2 for y in V] for x in V]
    r=rankF2(Bm)
    E=sum(p[c]*prod(p[c2]+1 for c2 in range(len(p)) if c2!=c) for c in range(len(p))); Vv=prod(q+1 for q in p)
    a=solve(V,lambda x,y: common(x,y)%2==m%2,0,0,1200)[0]
    o=solve(V,lambda x,y: common(x,y)%2==(m+1)%2,0,0,1200)[0]
    ok=(a,o,r,E-Vv+2)==(madm,moth,R,EV)
    print(p,len(V),(a,o,r,E-Vv+2),'OK' if ok else ('MISMATCH paper',madm,moth,R,EV),flush=True)
