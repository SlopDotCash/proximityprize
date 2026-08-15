#!/usr/bin/env python3
"""
Opus-core CORE probe (#509): does the DYADIC (2-power) structure of the smooth
subgroup <g>, order n=2m with g^m = -1, force an ARITHMETIC constraint on the
orbit-class mass profile (S0, (S_gamma)) beyond G88's Parseval identity?

Setup (exact, from _R308 / _G88):
  repRF(c) = #{ (t_1..t_r) in (Z/n)^r : sum_i g^{t_i} = c }  in F_q.
  g has order exactly n, and n = 2m with g^m = -1  (dyadic-friendly generator).
  Kernel-class mass S0 = repRF(0).
  For gamma in nonkernel n-th-power classes, S_gamma = n * repRF(c0)  (c0^n=gamma).
  Wall:  n*centeredShadowMass = q*( n*S0^2 + sum_gamma S_gamma^2 ) - n*n^{2r}.
  Prize (DCEnergyBound) needs:  centeredShadowMass <= q*(2r-1)!!*n^r.

Question this probe answers decisively:
  (A) Antipodal pairing g^{j+m} = -g^j means the r roots split by sign. Does this
      impose a PARITY/DIVISIBILITY constraint on repRF that a generic order-n
      subgroup would NOT have?  (thinness-essential arithmetic rigidity)
  (B) Compare the realized L2-profile  P := n*S0^2 + sum_gamma S_gamma^2  against:
        - the wall RHS the prize needs  W := n*(2r-1)!!*n^r + n^{2r}/q,
        - the Cauchy-Schwarz kernel-concentration bracket,
      at DYADIC n (2-powers) vs NON-dyadic even n vs ODD n (non-antipodal),
      to see if dyadic n is EXTREMAL/DISTINGUISHED for the profile.
  (C) Does the profile admit a non-Cauchy-Schwarz upper bound at dyadic n?
      i.e. is sum_gamma S_gamma^2 provably < concentration bracket by a gap that
      SCALES (would move the wall) or is it O(1)/artifact (no-go)?
"""
import itertools, math
from collections import Counter

def is_prime(x):
    if x < 2: return False
    for d in range(2, int(x**0.5)+1):
        if x % d == 0: return False
    return True

def find_gen_order_n(p, n):
    """Find g in F_p^* of order exactly n, with g^(n/2) = -1 (i.e. -1 in <g> at half)."""
    if (p-1) % n != 0: return None
    # primitive root
    def order(a):
        o=1; x=a%p
        while x!=1:
            x=(x*a)%p; o+=1
            if o>p: return None
        return o
    for a in range(2,p):
        if order(a)==p-1:
            g=pow(a,(p-1)//n,p)
            if order(g)==n:
                # check g^(n/2) == p-1 (-1)
                if n%2==0 and pow(g,n//2,p)==p-1:
                    return g
                if n%2==1:
                    return g  # odd: no antipodal structure
    return None

def repRF_profile(p, g, n, r):
    """Compute repRF(c) for all c, via r-fold convolution of the root indicator."""
    roots=[pow(g,t,p) for t in range(n)]
    # distribution of single g^t : each root once (roots distinct since order n)
    dist=Counter(roots)  # value -> count (all 1)
    cur=Counter({0:1})
    for _ in range(r):
        nxt=Counter()
        for v,cv in cur.items():
            for rt,crt in dist.items():
                nxt[(v+rt)%p]+= cv*crt
        cur=nxt
    return cur  # c -> repRF(c)

def analyze(p, n, r, label):
    g=find_gen_order_n(p,n)
    if g is None: return None
    rep=repRF_profile(p,g,n,r)
    S0=rep.get(0,0)
    # orbit classes: group nonkernel values by n-th power (class label c^n)
    classes=Counter()  # label -> total repRF mass in the class fiber
    fibersize=Counter()
    for c in range(1,p):
        lbl=pow(c,n,p)
        classes[lbl]+=rep.get(c,0)
        fibersize[lbl]+=1
    # Each nonkernel class fiber should have exactly n elements; S_gamma = class mass
    Sg=list(classes.values())
    P = n*S0*S0 + sum(s*s for s in Sg)     # profile L2 quantity
    q=p
    # centeredShadowMass from wall
    csm = (q*(n*S0*S0 + sum(s*s for s in Sg)) - n*(n**(2*r)))/n
    # prize wall RHS
    def dfact(k):
        r_=1
        while k>0: r_*=k; k-=2
        return r_
    prize_rhs = q*dfact(2*r-1)*(n**r)
    # cauchy-schwarz concentration bracket on centeredShadowMass
    total_nonkernel_mass = sum(Sg)  # = n^r - S0
    conc = (q*(n*S0*S0 + total_nonkernel_mass**2) - n*(n**(2*r)))/n
    # equidistribution (min) bracket
    numcl=len(Sg)
    equi = (q*(n*S0*S0 + (total_nonkernel_mass**2)/numcl) - n*(n**(2*r)))/n if numcl else 0
    # PARITY / divisibility test on repRF values (dyadic signature?)
    repvals=[rep.get(c,0) for c in range(1,p)]
    gcd_all=0
    for v in repvals+[S0]:
        gcd_all=math.gcd(gcd_all,v)
    return dict(label=label,p=p,n=n,r=r,g=g,S0=S0,numclasses=numcl,
               fiber_ok=all(fs==n for fs in fibersize.values()),
               Sg_min=min(Sg) if Sg else 0, Sg_max=max(Sg) if Sg else 0,
               P=P, csm=csm, prize_rhs=prize_rhs, conc=conc, equi=equi,
               csm_le_prize=(csm<=prize_rhs),
               gcd_repRF=gcd_all,
               csm_over_prize=csm/prize_rhs if prize_rhs else float('inf'))

if __name__=="__main__":
    print("="*100)
    print("DYADIC vs NON-DYADIC orbit-class mass profile rigidity  (#509 CORE probe)")
    print("="*100)
    # dyadic n (2-powers) at moderate primes; compare same p across n if possible
    tests=[]
    # collect primes p with p-1 divisible by target n
    for n in [4,8,16]:
        for r in [2,3]:
            # find a few primes
            found=0
            for p in range(17, 4000):
                if not is_prime(p): continue
                if (p-1)%n!=0: continue
                res=analyze(p,n,r,f"dyadic n={n}")
                if res:
                    tests.append(res); found+=1
                if found>=3: break
    # non-dyadic even n (has -1? only if n even AND g^{n/2}=-1 which is automatic for even n in cyclic group; 
    # to break antipodal structure use ODD n)
    for n in [3,5,9]:
        for r in [2,3]:
            found=0
            for p in range(17,4000):
                if not is_prime(p): continue
                if (p-1)%n!=0: continue
                res=analyze(p,n,r,f"ODD n={n} (no antipodal)")
                if res:
                    tests.append(res); found+=1
                if found>=2: break
    hdr=f"{'label':22} {'p':>6} {'n':>3} {'r':>2} {'S0':>7} {'#cl':>5} {'fiberOK':>7} {'gcd':>4} {'csm':>14} {'prize':>14} {'csm/prize':>9} {'<=prize':>7}"
    print(hdr); print("-"*len(hdr))
    for t in tests:
        print(f"{t['label']:22} {t['p']:>6} {t['n']:>3} {t['r']:>2} {t['S0']:>7} {t['numclasses']:>5} {str(t['fiber_ok']):>7} {t['gcd_repRF']:>4} {t['csm']:>14.1f} {t['prize_rhs']:>14.1f} {t['csm_over_prize']:>9.3f} {str(t['csm_le_prize']):>7}")
    print()
    print("KEY QUESTIONS:")
    print(" 1. gcd(repRF) column: is there a DYADIC-specific divisor of all repRF values")
    print("    (would be a thinness arithmetic constraint) vs gcd=1 generically?")
    print(" 2. csm/prize < 1 always? and is the margin structural or does it approach 1")
    print("    (approaching 1 = wall is tight = prize barely holds; >1 = would refute).")
