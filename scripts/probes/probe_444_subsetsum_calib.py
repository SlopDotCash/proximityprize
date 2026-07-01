# Reproduce the in-tree DeepBandR3 calibration EXACTLY via its actual model:
#   the monic codeword-stack X^{k+1}+gamma X^k - W (k=r-1), Vieta-pinned
#   gamma = -sum_{z in S} z  (negative subset sum, e_1(S)).
#   #bad = #distinct values of (-sum S) over (r+1)-subsets S of mu_n.
# Target r=3: #bad = n*C(n/4,2)+1 = 97 (n=16), 897 (n=32). O_P=C(n/4,2)=6,28.
from math import comb, gcd
from itertools import combinations
import sys
P1=2013265921; P2=3221225473
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def subsetsum_census(n,p,r):
    a=r+1; dom=mu_n(n,p)
    fiber={}
    for S in combinations(range(n),a):
        g=(-sum(dom[i] for i in S))%p
        fiber[g]=fiber.get(g,0)+1
    nd=len(fiber)
    has_zero = 1 if (0 in fiber) else 0
    nz=sum(1 for g in fiber if g!=0)
    return nd, has_zero, nz, fiber
for n in [int(x) for x in sys.argv[1:]] or [16]:
    for p,tag in [(P1,"P1"),(P2,"P2")]:
        nd,hz,nz,fiber=subsetsum_census(n,p,3)
        target=n*comb(n//4,2)+1
        OP=nz//n  # dilation orbit size = n (gcd issue: subset-sum gamma scales as g^1, d=gcd(1,n)=1)
        print(f"n={n} {tag} r=3 SUBSET-SUM model: #distinct gamma={nd} target(n*C(n/4,2)+1)={target} match={nd==target}")
        print(f"   nonzero={nz} zero_present={hz} O_P=nz/n={nz/n} (target C(n/4,2)={comb(n//4,2)})")
        # fiber distribution
        from collections import Counter
        szc=Counter(fiber.values())
        print(f"   fiber-size dist (size->#gamma): {dict(sorted(szc.items()))}")
