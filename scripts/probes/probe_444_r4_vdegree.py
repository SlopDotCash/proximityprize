# Probe V's "degree" / low-degree structure at r=4, n=16 (exhaustive).
# Decompose V = {he*hf1 = hf*he1} into:
#   (A) he=0 AND hf=0           -> inf pins (the gamma undefined locus)
#   (B) he=0 AND hf!=0          -> gamma=0 component
#   (C) he!=0,hf!=0, identity   -> genuinely pinned nonzero gamma
# Question: is (C) governed by a lower-degree handle? Check antipodal-pair content of S,
# and whether the special LARGE-fiber orbit = subsets that are unions of mu_d-cosets.
from math import comb, gcd
from itertools import combinations
from collections import Counter
P1=2013265921
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def hser(elts,mmax,p):
    H=[0]*(mmax+1); H[0]=1
    for z in elts:
        for m in range(1,mmax+1):
            H[m]=(H[m]+z*H[m-1])%p
    return H
n=16; p=P1; r=4; a=r+1; e=n//2+2; f=n//4+1
ie,ie1,jf,jf1=e-r,e-r+1,f-r,f-r+1; mmax=max(ie,ie1,jf,jf1)
dom=mu_n(n,p)
clsA=0; clsB=0; clsC=0
# antipodal pair: indices i,j with j=i+n/2 (z_j=-z_i). count antipodal pairs in S.
def antipodal_pairs(S):
    Sset=set(S); cnt=0
    for i in S:
        if (i+n//2)%n in Sset and i < (i+n//2)%n: cnt+=1
    return cnt
fiberC=Counter()
# track special large-fiber gammas' subsets
gamma_subsets={}
for S in combinations(range(n),a):
    elts=[dom[i] for i in S]; H=hser(elts,mmax,p)
    he,he1,hf,hf1=H[ie],H[ie1],H[jf],H[jf1]
    if (he*hf1-hf*he1)%p==0:
        if he%p==0 and hf%p==0: clsA+=1
        elif he%p==0: clsB+=1
        else:
            clsC+=1
            g=(-he*pow(hf,p-2,p))%p
            fiberC[g]+=1
            gamma_subsets.setdefault(g,[]).append(S)
print(f"n={n} r=4 line(x^{e},x^{f}) V-decomposition:")
print(f"  (A) he=0 & hf=0 (inf pins): {clsA}")
print(f"  (B) he=0 & hf!=0 (gamma=0): {clsB}")
print(f"  (C) generic pinned nonzero: {clsC}")
print(f"  total V = {clsA+clsB+clsC}")
# special large-fiber gammas (size 2 at n=16)
big=[(c,g) for g,c in fiberC.items() if c>=2]
print(f"  #gammas with fiber>=2: {len(big)}  (the special orbit, size n/d should be 16)")
# For one big-fiber gamma, examine its subsets' antipodal structure
if big:
    big.sort(reverse=True)
    c,g=big[0]
    Ss=gamma_subsets[g]
    print(f"  example big-fiber gamma fiber size={c}; its {len(Ss)} subsets:")
    for S in Ss:
        ap=antipodal_pairs(S)
        # gaps between consecutive indices (coset structure)
        print(f"    S={S} antipodal_pairs={ap} sorted_diffs={sorted((S[i+1]-S[i]) for i in range(len(S)-1))}")
# overall antipodal-content of class C
apcount=Counter()
for g,Ss in gamma_subsets.items():
    for S in Ss:
        apcount[antipodal_pairs(S)]+=1
print(f"  class-C antipodal-pair-count distribution: {dict(sorted(apcount.items()))}")
