import itertools, subprocess, sys, json, time
MC=__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/c/mc'
def common(x,y):
    # x,y tuples of letters; count positions i with x_i==y_i and equal prefix multisets
    from collections import Counter
    cx=Counter(); cy=Counter(); c=0
    for a,b in zip(x,y):
        if a==b and cx==cy: c+=1
        cx[a]+=1; cy[b]+=1
    return c
def common2(x,y):
    # binary words fast: prefix weights
    c=0; wx=0; wy=0
    for a,b in zip(x,y):
        if a==b and wx==wy: c+=1
        wx+=a; wy+=b
    return c
def solve(V, edge, mode=0, target=0, tl=1e9):
    n=len(V)
    lines=[]
    for i in range(n):
        lines.append(''.join('1' if (i!=j and edge(V[i],V[j])) else '0' for j in range(n)))
    inp=f"{n} {mode} {target}\n"+"\n".join(lines)+"\n"
    out=subprocess.run([MC,str(tl)],input=inp.encode(),capture_output=True).stdout.decode().split()
    return int(out[0]), int(out[1]), int(out[2])
def paths(a,b): return [w for w in itertools.product((0,1),repeat=a+b) if sum(w)==b]
def rect(a,b,which,tl=600,mode=0,target=0):
    V=paths(a,b); m=a+b; par=(m if which=='M' else m+1)%2
    return solve(V, lambda x,y: common2(x,y)%2==par, mode,target,tl)
if __name__=='__main__':
    task=sys.argv[1]
    if task=='rect':
        tab={}
        for a in range(1,8):
            for b in range(1,a+1):
                if a+b>12: continue
                for which in ('M','Ms'):
                    if which=='M' and a==b: continue   # theorem: 2^n
                    t=time.time(); r=rect(a,b,which,tl=float(sys.argv[2]))
                    print(a,b,which,r,round(time.time()-t,1),flush=True)
    if task=='tworows':
        for a in range(2,int(sys.argv[2])+1):
            r1=rect(a,2,'M',tl=600); r2=rect(a,2,'Ms',tl=600); print(a,'M',r1,'Ms',r2,flush=True)
    if task=='rows':
        b=int(sys.argv[2])
        for a in range(int(sys.argv[3]),int(sys.argv[4])+1):
            print(a,b,'Ms',rect(a,b,'Ms',tl=float(sys.argv[5])),flush=True)
    if task=='oddsq':
        for n in range(1,int(sys.argv[2])+1):
            print(n,'Modd',rect(n,n,'Ms',tl=float(sys.argv[3])),flush=True)
    if task=='catalan':
        for n in range(1,int(sys.argv[2])+1):
            print(n,'even 2^n families count', rect(n,n,'M',tl=3000,mode=1,target=2**n),flush=True)
    if task=='oddcat':
        for n in range(1,int(sys.argv[2])+1):
            print(n,'odd families (n+1,n) of size 2^n count', rect(n+1,n,'M',tl=3000,mode=1,target=2**n),flush=True)
    if task=='freeend':
        for m in range(1,int(sys.argv[2])+1,2):
            V=list(itertools.product((0,1),repeat=m))
            print(m,'free-end odd max', solve(V, lambda x,y: common2(x,y)%2==1, 0,0,float(sys.argv[3])),flush=True)
