# Verify: for every noncrossing perfect matching M of [2n], the pairing construction gives s=ceil(log2 n) words of F_M
# lying in no other extremal family; and for M0 no set of fewer words works (n<=7 exhaustive for M0).
import itertools, math
def ncpm(n):
    if n==0: yield []; return
    # first point 1 matched with 2k
    for k in range(1,n+1):
        for A in ncpm(k-1):
            for B in ncpm(n-k):
                yield [(1,2*k)]+[(a+1,b+1) for a,b in A]+[(a+2*k,b+2*k) for a,b in B]
def construct(M,n):
    s=max(1,math.ceil(math.log2(n))) if n>=2 else 0
    arcs=sorted(M)
    pairs=[arcs[i:i+2] for i in range(0,len(arcs),2)]
    vecs=[v for v in itertools.product((0,1),repeat=s) if v[0]==0]  # class representatives
    assert len(pairs)<=len(vecs)
    col={}
    for c,grp in enumerate(pairs):
        v=vecs[c]; vb=tuple(1-x for x in v)
        a=grp[0]; col[a[0]]=v; col[a[1]]=vb
        if len(grp)==2:
            b=grp[1]
            nested = a[0]<b[0]<b[1]<a[1]
            if nested: col[b[0]]=v; col[b[1]]=vb
            else: col[b[0]]=vb; col[b[1]]=v
    words=[tuple(col[p][r] for p in range(1,2*n+1)) for r in range(s)]
    return words
for n in range(2,9):
    Ms=list(ncpm(n)); mx=0
    for M in Ms:
        W=construct(M,n)
        cnt=0
        for M2 in Ms:
            if all(all(w[a-1]!=w[b-1] for a,b in M2) for w in W): cnt+=1
        assert cnt==1,(n,M)
    print("n=",n,"C_n=",len(Ms),"construction with",math.ceil(math.log2(n)),"words determines every family")
# lower bound check: M0 with fewer than ceil(log2 n) words impossible (exhaustive for n<=6)
for n in range(2,7):
    Ms=list(ncpm(n)); M0=[(2*i-1,2*i) for i in range(1,n+1)]
    s=math.ceil(math.log2(n))-1
    FM=[w for w in itertools.product((0,1),repeat=2*n) if all(w[a-1]!=w[b-1] for a,b in M0)]
    ok=True
    for P in itertools.combinations(FM,s):
        cnt=sum(1 for M2 in Ms if all(all(w[a-1]!=w[b-1] for a,b in M2) for w in P))
        if cnt==1: ok=False;break
    print("n=",n,"M0 not determined by",s,"words:",ok)
