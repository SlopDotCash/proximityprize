"""
Diagnose the n=16 r=6 gamma-fiber anomaly: 8 gammas have fiber 112 (= #bad). What are they?
Also: O_P (orbit count) vs #bad, and how the big-fiber gammas relate to dilation fixed points.
gamma(gS)=g^{e-f} gamma(S), e-f=2, d=gcd(2,16)=2 => dilation by g multiplies gamma by g^2.
The subgroup {g^2} has order n/d=8. gamma in a coset of <w^2>-action; fixed points where g^2=1
i.e. g in {1, w^{8}} (the order-2 elt) act, gamma*w^16=gamma etc. Let's just enumerate.
"""
import itertools
from math import comb, gcd
from collections import Counter, defaultdict
p=2013265921
def w_of_order(n,P):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return h
    raise RuntimeError
def complete_homog(S,mmax,P):
    PS=[0]*(mmax+1)
    for z in S:
        zi=1
        for j in range(1,mmax+1): zi=(zi*z)%P; PS[j]=(PS[j]+zi)%P
    h=[0]*(mmax+1); h[0]=1
    for m in range(1,mmax+1):
        s=0
        for i in range(1,m+1): s=(s+PS[i]*h[m-i])%P
        h[m]=(s*pow(m,P-2,P))%P
    return h
n=16; r=6; e,f=12,10; a0=7; P=p
w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
i1,i2,i3,i4=e-r,e-r+1,f-r,f-r+1
inv=lambda x:pow(x,P-2,P)
fib=defaultdict(list)
for Sidx in itertools.combinations(range(n),a0):
    S=[mu[i] for i in Sidx]
    h=complete_homog(S,max(i1,i2,i3,i4),P)
    he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
    if (he_r*hf_r1-hf_r*he_r1)%P!=0: continue
    if hf_r%P!=0: g=(-he_r*inv(hf_r))%P
    elif hf_r1%P!=0: g=(-he_r1*inv(hf_r1))%P
    else: continue
    if g!=0: fib[g].append(Sidx)
sizes=Counter(len(v) for v in fib.values())
print("fiber sizes:",dict(sorted(sizes.items())))
# the big-fiber gammas:
big=[g for g,v in fib.items() if len(v)==112]
print(f"#gammas with fiber 112: {len(big)}")
mult=mu[(e-f)%n]  # w^2
# dilation orbit of a gamma under g->g^2*gamma: actually gamma(gS)=g^(e-f) gamma. So acting by w^t
# sends gamma -> w^(2t) gamma. orbit of gamma = {w^(2t) gamma}. order of w^2 = 8.
def orbit(g):
    o=set(); cur=g
    for _ in range(n): o.add(cur); cur=cur*mult%P
    return o
# how many distinct orbits among ALL distinct gammas, and among big ones?
allg=set(fib.keys()); rem=set(allg); orbs=0; orbit_reps=[]
while rem:
    x=next(iter(rem)); o=orbit(x); orbs+=1; orbit_reps.append((x,len(o & allg),len(o))); rem-=o
print(f"#distinct gamma={len(allg)}  #orbits O_P={orbs}")
# is each gamma-value's fiber = union over its orbit? check: do the 8 big-fiber gammas form orbits?
bigset=set(big)
remb=set(big); borb=0
while remb:
    x=next(iter(remb)); o=orbit(x); borb+=1; remb-=o
print(f"the {len(big)} fiber-112 gammas form {borb} orbit(s); are they orbit of size {len(orbit(big[0])&bigset)}?")
# relate big gamma to special values: is big gamma a root of unity / equals +-1?
for g in sorted(big)[:8]:
    # order of g in F_p^*? check small
    isrootunity = pow(g,n,P)==1
    print(f"  big gamma={g}  g^n==1?{isrootunity}  g==1?{g==1}  g==p-1(-1)?{g==P-1}")
# fiber size vs orbit: the SMALL-fiber gammas (size 2) -- orbit size of those?
small=[g for g,v in fib.items() if len(v)==2][:3]
for g in small:
    print(f"  small-fiber gamma={g} fiber=2, dilation-orbit-size={len(orbit(g))}, #its-orbit-in-allg={len(orbit(g)&allg)}")
