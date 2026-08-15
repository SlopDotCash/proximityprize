#!/usr/bin/env python3
"""
SKEPTIC re-derivation of Lane B (transfer operator).
Three targeted checks the worker's probes did NOT decisively make:

 (A) Vacuity of the (E2,E3)-grouping analysis: at n=32 do ANY two primes share (E2,E3)?
     If not, the worker's "M varies within a group / corr(M,E4)" reading printed on ZERO data.

 (B) The REAL gauge question for a TRANSFER OPERATOR: the tower step needs the JOINT
     distribution of (eta_b, eta_{gb}) (worker's Task 1 admits this). Is that joint object
     a function of the marginal magnitude multiset {|eta_b|} (=> gauge, worker right), or does
     it carry phase/correlation info the moment ladder does NOT see? We test: build two primes
     with (nearly) matching |eta| multiset-moments and compare the JOINT second moment
     C := (1/m) sum_b |eta_b|^2 |eta_{gb}|^2  (the operator's leading L2->L2 kernel entry).
     If C is a function of the marginals alone it is gauge; if it varies independently, CRACK.

 (C) Sanity: reproduce the transient ratios at n=128 for one deep prime, independent code path.
Regime: proper subgroup mu_n < F_p^*, p>=n^4, p==1 mod n, multiple primes, exclude X^{n/2}=+-1 dirs.
"""
import math, cmath
import numpy as np

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def v2(x):
    k=0
    while x%2==0:k+=1;x//=2
    return k

def primroot(p):
    fac=set();mm=p-1;d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac):return a

def find_prime(n,beta=4,extra_v2=0,start_mult=1):
    base=((n**beta//n)+start_mult)*n+1;p=base;need=v2(n)+extra_v2
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and v2(p-1)>=need:return p
        p+=n

def subgroup(p,n):
    g=primroot(p);h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

def eta_complex_cosets(p,S,n,g=None):
    """Return complex eta_b over the m cosets b=g^i, i=0..m-1 (b!=0)."""
    if g is None:g=primroot(p)
    m=(p-1)//n
    Sarr=np.array(S,dtype=np.int64)
    breps=np.empty(m,dtype=np.int64);b=1
    for i in range(m):breps[i]=b;b=(b*g)%p
    tp=2*np.pi/p
    re=np.empty(m);im=np.empty(m)
    CH=max(1,4_000_000//max(1,len(Sarr)))
    for lo in range(0,m,CH):
        hi=min(m,lo+CH)
        ph=tp*((breps[lo:hi,None]*Sarr[None,:])%p)
        re[lo:hi]=np.cos(ph).sum(1);im[lo:hi]=np.sin(ph).sum(1)
    return re+1j*im, breps, g

print("="*78);print("(A) Does ANY pair of primes at n=32 share (E2,E3)? (worker grouping vacuity)");print("="*78)
n=1<<5
rows=[];p=find_prime(n,beta=4);cnt=0
while cnt<14:
    if isprime(p) and (p-1)%n==0 and v2(p-1)>=v2(n):
        S=subgroup(p,n)
        av=np.abs(eta_complex_cosets(p,S,n)[0])
        E2=round(n*float(np.sum(av**4)));E3=round(n*float(np.sum(av**6)))
        E4=round(n*float(np.sum(av**8)));M=float(np.max(av))
        rows.append((p,E2,E3,E4,M));cnt+=1
    p+=n
from collections import defaultdict
grp=defaultdict(list)
for r in rows:grp[(r[1],r[2])].append(r)
ndup=sum(1 for k,v in grp.items() if len(v)>1)
print(f"  {len(rows)} primes, {len(grp)} distinct (E2,E3) keys, {ndup} keys with >1 prime.")
print(f"  => worker's within-(E2,E3) 'M varies / corr(M,E4)' analysis ran on {ndup} groups.")
if ndup==0:
    print("  *** VACUOUS: the printed 'Reading' is boilerplate, not supported by any grouped data.")

print("\n"+"="*78);print("(B) TRANSFER gauge: is joint C=<|eta_b|^2 |eta_gb|^2> a fn of marginals?");print("="*78)
print("  Compare across primes: does the JOINT cross-coset 2nd moment carry info beyond the")
print("  marginal |eta| moment ladder? We report C_norm = C / (mean|eta|^2)^2 (=1 if independent).")
print(f"  {'p':>10} {'v2':>3} {'E2/n':>12} {'meanA2':>10} {'C':>14} {'C/(meanA2)^2':>13}")
for (p,E2,E3,E4,M) in rows[:8]:
    S=subgroup(p,n)
    eta,breps,g=eta_complex_cosets(p,S,n)
    A2=np.abs(eta)**2
    m=len(eta)
    # gb maps coset i -> coset i+1 (since b=g^i, gb=g^{i+1}); wraps mod m
    A2g=np.roll(A2,-1)
    C=float(np.mean(A2*A2g))
    meanA2=float(np.mean(A2))
    print(f"  {p:>10} {v2(p-1):>3} {E2//n:>12} {meanA2:>10.4f} {C:>14.4f} {C/meanA2**2:>13.6f}")
print("""
  READ: eta_{gb} where gb=g^{i+1} — but note b -> gb is the coset SHIFT, and the correlation
  between adjacent cosets is what the TOWER STEP eta_b(2N)=eta_b(N)+eta_gb(N) actually uses.
  If C/(meanA2)^2 == 1 (adjacent cosets uncorrelated) across all primes AND equals the marginal
  prediction, the joint is gauge. If it deviates and VARIES beyond what marginals fix, that is the
  surviving crack the worker's marginal-multiset argument misses.
""")

print("="*78);print("(C) Independent reproduction of transient ratio at deep prime (n up to 128)");print("="*78)
p=find_prime(1<<7,beta=4,extra_v2=0);g=primroot(p);A=v2(p-1)
print(f"  p={p}, v2={A}, m_top={(p-1)//128}")
prevM=None
for j in range(1,min(A,7)+1):
    nn=1<<j
    S=[pow(g,((p-1)//nn)*i,p) for i in range(nn)]
    M=float(np.max(np.abs(eta_complex_cosets(p,S,nn,g=g)[0])))
    rt=M/prevM if prevM else float('nan')
    print(f"  j={j} n={nn:>4} M={M:>10.4f} M/sqrt(n)={M/math.sqrt(nn):>8.4f} ratio={rt:>8.4f} /sqrt2={rt/math.sqrt(2) if prevM else float('nan'):>8.4f}")
    prevM=M
