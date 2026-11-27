import sys
from math import comb
from fractions import Fraction as Fr
from flint import fmpz_mat
def C(n,k): return comb(n,k) if 0<=k<=n else 0
exec(open(__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/v3_canon.py').read().split('def brute')[0])  # import dp
def multisum(k):
    if k==0: return 1
    tot=Fr(C(2*k,k),k+1)
    for b in range(1,k):
        for c in range(0,b+1):
            for r in range(b,k):
                n1=2*k-b-c; n2=r+b-1; n3=k-1-r+c
                tot+=Fr(b-c+1,k-c+1)*C(n1,k-b)*Fr(r-b+2,r+1)*C(n2,b-1)*C(n3,c)
    assert tot.denominator==1
    return int(tot)
Q=[1]+[sum(dp(k,'321')) for k in range(1,25)]
paper=[1,1,5,33,234,1706,12618,94157,706878,5330403,40332881,306023196,2327290506,17734226120,135376087792,1035065812309,7925664456804,60771825678389,466587436417569,3586731522598141,27604168028694252,212685629040409758,1640473066548280308,12666272996480868428,97894846717057492194]
assert Q==paper, [ (i,a,b) for i,(a,b) in enumerate(zip(Q,paper)) if a!=b]
assert all(multisum(k)==Q[k] for k in range(0,25))
print("Q_0..Q_24 match paper; multisum (Shankar Thm 7.1 as stated) matches DP for k<=24")
H1=fmpz_mat([[Q[i+j+1] for j in range(12)] for i in range(12)]).det()
H0=fmpz_mat([[Q[i+j] for j in range(13)] for i in range(13)]).det()
print("det(Q_{i+j+1})_{12x12} =",H0 if False else H1); print("det(Q_{i+j})_{13x13} =",H0)
assert int(H1)==-16871599970737005465806167716982557747256 and int(H0)==-169232977731413820207351628133858712800869482
lead0=[int(fmpz_mat([[Q[i+j] for j in range(N)] for i in range(N)]).det()) for N in range(1,14)]
lead1=[int(fmpz_mat([[Q[i+j+1] for j in range(N)] for i in range(N)]).det()) for N in range(1,13)]
print("signs leading H0 N=1..13:",[1 if v>0 else -1 for v in lead0]); print("signs leading H1 N=1..12:",[1 if v>0 else -1 for v in lead1])
# B_k Hankel (should be positive) 
Bs=[1]+[sum(dp(k,'231')) for k in range(1,25)]
print("B_k:",Bs[:10])
lb0=[int(fmpz_mat([[Bs[i+j] for j in range(N)] for i in range(N)]).det()) for N in range(1,13)]
lb1=[int(fmpz_mat([[Bs[i+j+1] for j in range(N)] for i in range(N)]).det()) for N in range(1,12)]
print("B Hankel all positive:", all(v>0 for v in lb0+lb1))
# asymptotics: k Q_k / 8^k via multisum is O(k^3); use DP sum (fast) for larger k
import math
for k in (25,50,100,200,400):
    q=sum(dp(k,'321'))
    print(k, "kQ_k/8^k =", q*k/8**k, " (2/pi=",2/math.pi,")")
