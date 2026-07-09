#!/usr/bin/env python3
"""
C040 CRUX: does the 'subtract n^{2r} first' reframing actually buy anything for the moment bound?

The whole moment method needs  E_r <= (2r-1)!! * n^r  (GaussianEnergyBound). The achievable B is
  B^{2r} <= sum_{b!=0} |eta_b|^{2r} = q*E_r - n^{2r}   (this is the 'cumulant' kappa_r in C040).
So  B <= (q*E_r - n^{2r})^{1/2r}.

C040 says: kappa_r / baseline (=q*(2r-1)!!*n^r) stays <= 1, so B <= (q*(2r-1)!!*n^r)^{1/2r}, the prize.
For that to be TRUE and USEFUL we need:  q*E_r - n^{2r} <= q*(2r-1)!!*n^r,  i.e.
        E_r <= (2r-1)!!*n^r + n^{2r}/q.                         (*)

Two facts decide whether C040 is a real saving:
  (A) Is E_r^{C} (char-0) itself <= (2r-1)!!*n^r ? If YES, (*) holds for free in char 0 (defect aside)
      and the 'first subtract n^{2r}' is irrelevant -- the bound was already there. If NO, the cumulant
      reframing CANNOT rescue it because subtracting n^{2r} (a constant indep of where E_r sits) does
      not change E_r.
  (B) In the prize regime the defect D_r = E_r^{Fq} - E_r^{C} -- is it really negative (helping (*)),
      or 0 (no help), or positive (the wall)? We measure exactly.

We print, per (n, beta): E_r^{Fq}, the char-0 baseline (2r-1)!!*n^r, the RATIO E_r^{Fq}/baseline and
E_r^{C}/baseline, and B_achieved = (q*E_r^{Fq}-n^{2r})^{1/2r} vs B_target = sqrt(2 n ln q) and the true
max |eta_b| (B_true) by direct computation.
"""
import math, itertools, cmath
from fractions import Fraction
from collections import defaultdict

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def prime_1_mod_n_near(target, n):
    p = target - (target % n) + 1
    while not is_prime(p): p += n
    return p

def order_n_gen(p, n):
    for g in range(2, p):
        h = pow(g,(p-1)//n,p)
        s=set(); x=1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return h
    return None

def dfac2(r):
    x=1
    for i in range(1,r+1): x*=(2*i-1)
    return x

def Er_Fq_exact(p,n,h,rmax):
    mu=[pow(h,i,p) for i in range(n)]
    R=[0]*p
    for x in mu: R[x]+=1
    Es={}; cur=R[:]
    for r in range(1,rmax+1):
        Es[r]=sum(c*c for c in cur)
        if r<rmax:
            nxt=[0]*p
            for v in range(p):
                cv=cur[v]
                if cv:
                    for x in mu: nxt[(v+x)%p]+=cv
            cur=nxt
    return Es

def Er_char0_exact(n,rmax,cap=5_000_000):
    pts=[cmath.exp(2j*math.pi*i/n) for i in range(n)]
    res={}
    for r in range(1,rmax+1):
        if n**r>cap: res[r]=None; continue
        cnt=defaultdict(int)
        for combo in itertools.product(range(n),repeat=r):
            s=sum(pts[i] for i in combo)
            cnt[(round(s.real,7),round(s.imag,7))]+=1
        res[r]=sum(v*v for v in cnt.values())
    return res

def max_eta(p,n,h):
    mu=[pow(h,i,p) for i in range(n)]
    best=0.0
    for b in range(1,p):
        s=sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in mu)
        m=abs(s)
        if m>best: best=m
    return best

print("="*120)
print("C040 CRUX: is E_r^C <= (2r-1)!! n^r ? and does subtracting n^{2r} first ever help the bound?")
print("="*120)

for n in (8,16):
    rmax = 6 if n==8 else 5
    Ec = Er_char0_exact(n,rmax)
    print(f"\n{'#'*100}\nn={n}")
    print("  char-0 ratio  E_r^C / ((2r-1)!! n^r):")
    for r in range(1,rmax+1):
        if Ec.get(r) is None: continue
        ratio = Ec[r]/(dfac2(r)*n**r)
        print(f"    r={r}: E_r^C={Ec[r]:>14}  baseline (2r-1)!! n^r = {dfac2(r)*n**r:>14}  ratio={ratio:.4f}  {'<=1 OK' if ratio<=1 else '>1 *** char-0 ALREADY exceeds Gaussian baseline ***'}")
    for beta in (4.0, 5.0):
        target=int(round(n**beta))
        if target>2_000_000: continue
        p=prime_1_mod_n_near(target,n)
        if p>2_000_000: continue
        h=order_n_gen(p,n)
        Efq=Er_Fq_exact(p,n,h,rmax)
        lnq=math.log(p)
        Btrue = max_eta(p,n,h) if p<200_000 else None
        print(f"\n  beta={beta} p={p} (log_n p={math.log(p)/math.log(n):.3f})  sqrt(2 n ln q)={math.sqrt(2*n*lnq):.3f}  sqrt n={math.sqrt(n):.3f}" +
              (f"  B_true(max|eta|)={Btrue:.4f}" if Btrue else ""))
        print(f"    {'r':>2} {'E_r^Fq/base':>12} {'E_r^C/base':>11} {'defect D_r':>14} {'kap/qbase':>10} {'B_ach=(qE-n^2r)^{1/2r}':>22}")
        for r in range(1,rmax+1):
            if Ec.get(r) is None:
                continue
            base = dfac2(r)*n**r
            efq_ratio = Efq[r]/base
            ec_ratio  = Ec[r]/base
            D = Efq[r]-Ec[r]
            kap = p*Efq[r]-n**(2*r)
            qbase = p*base
            B_ach = (kap)**(1.0/(2*r)) if kap>0 else 0.0
            print(f"    {r:>2} {efq_ratio:>12.4f} {ec_ratio:>11.4f} {D:>14} {kap/qbase:>10.4f} {B_ach:>22.4f}")
print("""
DECISION:
- If E_r^C / baseline > 1 (char-0 already exceeds the Gaussian baseline), then GaussianEnergyBound is
  FALSE in char 0 at that r, and subtracting n^{2r} (which is irrelevant to where E_r sits) cannot fix it.
  The moment bound that yields the prize REQUIRES E_r ~ (2r-1)!! n^r; if char-0 E_r already overshoots,
  the 'cumulant' reframing is empty.
- The B_ach column is the ACTUAL achievable bound from the cumulant. Compare to sqrt(2 n ln q): the prize
  target. The minimum over r of B_ach is what the method gives.
""")
