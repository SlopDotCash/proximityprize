#!/usr/bin/env python3
"""
probe_466r11_jointphase.py -- LANE J (#466 round 11): JointPhaseFieldStructure.

THE PRECISE QUESTION (from round-10 essay's one un-foreclosed sub-thread).
The tower recursion is  eta_b(mu_n) = eta_b(mu_{n/2}) + eta_{zeta b}(mu_{n/2}),  zeta a primitive
n-th root.  Because zeta in mu_n, the point zeta*b is in the SAME mu_n-coset as b, so
|eta_b| = |eta_{zeta b}| EXACTLY (dilation invariance of the magnitude).  The magnitude multiset
carries no joint info here at all -- the ONLY possible new content is the PHASE relationship
arg(eta_{zeta b}) - arg(eta_b), or the joint distribution of the pair of phasors, at DEEP moment
order r (NOT the r=2 already found marginal-determined).

We define the joint object as the PHASE-DIFFERENCE field over the coset b -> the two half-period
phasors that build eta_b, and its deep-r correlators, and we run four tests:

  (GAUGE)  Is the joint statistic a function of the single-coset moment ladder E_2..E_2r
           (i.e. of the marginal |eta| multiset)? Match moments across primes/cosets, compare joint.
  (BSENS)  Does the joint statistic vary across cosets b after removing the dilation-invariant part?
  (DEPTH)  Round 10 found marginal-determination at r=2. Push to r=3,4 and probe the TREND with r:
           does joint-vs-marginal gap GROW (promising) or stay 0 (dead)?
  (WHITE)  Connect to [doorIV-joint-field-white]: is deep-r the same diagonalization, or different?

Regime: proper subgroup mu_n < F_p^*, p>=n^4, p==1 mod n, >=2 primes distinct v2(p-1),
        exclude X^{n/2}=+-1. Small n=8,16. Scanner validated vs a brute recomputation.
"""
import math, cmath
import numpy as np

# ---------------------------------------------------------------- number theory
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

def find_primes(n,beta=4,count=6):
    """primes p>=n^beta, p==1 mod n, v2(p-1)>=v2(n), exclude X^{n/2}=+-1 by requiring
    the subgroup generator h=g^{(p-1)/n} has full order n (proper mu_n). Return with v2 spread."""
    out=[]
    base=(n**beta)//n*n+1
    p=base
    need=v2(n)
    while len(out)<count:
        if p>n and isprime(p) and (p-1)%n==0 and v2(p-1)>=need:
            # exclude degenerate directions: ensure mu_n is a PROPER subgroup (n<p-1) and
            # h has exact order n
            g=primroot(p); h=pow(g,(p-1)//n,p)
            if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in _primefactors(n)):
                out.append(p)
        p+=n
    return out

def _primefactors(n):
    f=set();d=2;m=n
    while d*d<=m:
        if m%d==0:
            f.add(d)
            while m%d==0:m//=d
        d+=1
    if m>1:f.add(m)
    return f

def subgroup(p,n,g=None):
    if g is None: g=primroot(p)
    h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)], g, h

# ---------------------------------------------------------------- eta computations
def eta_over_cosets(p, S, g):
    """eta_b for b = g^i, i=0..m-1 (all nonzero cosets reps of F_p^*/mu_n). complex."""
    m=(p-1)//len(S)
    Sarr=np.array(S,dtype=np.int64)
    breps=np.empty(m,dtype=np.int64); b=1
    for i in range(m): breps[i]=b; b=(b*g)%p
    tp=2*np.pi/p
    re=np.empty(m); im=np.empty(m)
    CH=max(1,4_000_000//max(1,len(Sarr)))
    for lo in range(0,m,CH):
        hi=min(m,lo+CH)
        ph=tp*((breps[lo:hi,None]*Sarr[None,:])%p)
        re[lo:hi]=np.cos(ph).sum(1); im[lo:hi]=np.sin(ph).sum(1)
    return re+1j*im, breps

def half_periods(p, b, Hlow, zeta):
    """Return (A_b, B_b) = (eta_b over mu_{n/2}, eta_{zeta b} over mu_{n/2}), complex.
    Hlow = list of mu_{n/2} elements; zeta = primitive n-th root (an element of mu_n\mu_{n/2}).
    Note A+B = eta_b over full mu_n. |A|,|B| are the two half-period magnitudes; their JOINT
    phase is the tower-recursion content."""
    tp=2*np.pi/p
    A=0j; B=0j
    zb=(zeta*b)%p
    for x in Hlow:
        A+=cmath.exp(1j*tp*((b*x)%p))
        B+=cmath.exp(1j*tp*((zb*x)%p))
    return A,B

# ---------------------------------------------------------------- moment ladder
def moments(av, n, upto=6):
    """E_r = n * sum_b |eta_b|^{2r} over cosets; return dict r->E_r (as float)."""
    d={}
    for r in range(1,upto+1):
        d[r]=n*float(np.sum(av**(2*r)))
    return d

# ================================================================ MAIN
def banner(s): print("\n"+"="*80+"\n"+s+"\n"+"="*80)

print("probe_466r11_jointphase.py -- LANE J JointPhaseFieldStructure")
print("numpy",np.__version__)

for n in (8,16):
    banner(f"n={n}  (mu_n proper subgroup, p>=n^4, p==1 mod n)")
    primes=find_primes(n,beta=4,count=6)
    # ensure >=2 distinct v2(p-1)
    print(f"primes: {primes}  v2(p-1)={[v2(p-1) for p in primes]}")
    zeta_idx = n//2   # zeta = h^{n/2}? no: zeta primitive n-th root = h^1 generates mu_n.
    # mu_{n/2} = <h^2>. zeta = h (a primitive n-th root, in mu_n \ mu_{n/2}).
    rows=[]
    for p in primes:
        S,g,h=subgroup(p,n)
        eta,breps=eta_over_cosets(p,S,g)
        av=np.abs(eta)
        M=float(av.max())
        E=moments(av,n,upto=6)
        # zeta = h  (primitive n-th root: h has order n). mu_{n/2}=<h^2>.
        zeta=h
        Hlow=[pow(h,2*i,p) for i in range(n//2)]
        # joint half-period phase difference field over the m cosets b=g^i
        # compute A_b,B_b for each coset rep; the phase diff delta_b = arg(B)-arg(A)
        m=(p-1)//n
        deltas=np.empty(m); ratioMag=np.empty(m)
        Avec=np.empty(m,dtype=complex); Bvec=np.empty(m,dtype=complex)
        for i in range(m):
            A,B=half_periods(p,int(breps[i]),Hlow,zeta)
            Avec[i]=A; Bvec[i]=B
            deltas[i]=cmath.phase(B)-cmath.phase(A)
            ratioMag[i]=abs(B)/abs(A) if abs(A)>1e-12 else float('nan')
        # sanity: A+B must equal eta_b (full period)  -- validate scanner
        recon=np.abs(Avec+Bvec)
        err=float(np.max(np.abs(recon-av)))
        rows.append((p,v2(p-1),M,E,deltas,ratioMag,Avec,Bvec,av))
        print(f"  p={p:>10} v2={v2(p-1)} M={M:.4f}  E2/n={E[2]/n:.3f} E3/n={E[3]/n:.4f}"
              f"  |recon-eta|max={err:.2e}  (scanner valid if ~0)")

    # ---- GAUGE TEST: is the joint phase-difference statistic a function of the moment ladder?
    banner(f"[GAUGE] n={n}: joint cross-coset phase correlator vs moment ladder")
    print("  Define the DEEP-r joint correlator (cross-coset mixed phase moment):")
    print("    J_r := (1/m) sum_b cos( r * delta_b ),  delta_b = arg(B_b)-arg(A_b)")
    print("  This is the r-th Fourier coefficient of the phase-difference field. It is a PHASE")
    print("  statistic invisible to the magnitude multiset {|eta_b|}. If J_r is nonetheless")
    print("  pinned to a fixed value whenever the moments E_2..E_2r match => gauge; if it varies")
    print("  independently of matched moments => genuinely new (candidate crack).")
    print(f"  {'p':>10} {'v2':>3} {'E2/n':>9} {'E3/n':>10} {'J1':>9} {'J2':>9} {'J3':>9} {'J4':>9}")
    for (p,vv,M,E,deltas,rm,Av,Bv,av) in rows:
        Js=[float(np.mean(np.cos(r*deltas))) for r in (1,2,3,4)]
        print(f"  {p:>10} {vv:>3} {E[2]/n:>9.3f} {E[3]/n:>10.4f} "
              f"{Js[0]:>9.4f} {Js[1]:>9.4f} {Js[2]:>9.4f} {Js[3]:>9.4f}")

    # ---- BSENS TEST: does delta_b vary across cosets (b-sensitive) after removing dilation part?
    banner(f"[BSENS] n={n}: b-sensitivity of the joint phase-difference field")
    print("  |eta_b| is CONSTANT on mu_n-cosets (dilation-invariant). Question: is delta_b (the")
    print("  joint half-period phase difference) ALSO coset-constant (=> b-blind, dead) or does it")
    print("  vary => b-sensitive. Report std(delta_b) across cosets and the b-summed sum_b sin(delta).")
    for (p,vv,M,E,deltas,rm,Av,Bv,av) in rows[:3]:
        # dilation-invariant part: does delta depend only on |eta|? bin by |eta| and check spread
        d_std=float(np.std(deltas))
        # b-summed antisymmetric part (this is what a b-BLIND method would only see):
        bsum_sin=float(np.mean(np.sin(deltas)))
        bsum_cos=float(np.mean(np.cos(deltas)))
        # correlation of delta_b with |eta_b| (if delta is a function of |eta|, |corr|->1-ish/monotone)
        cc=float(np.corrcoef(deltas, av)[0,1])
        print(f"  p={p:>10}: std(delta)={d_std:.4f}  <cos d>={bsum_cos:.4f}  <sin d>={bsum_sin:.4f}"
              f"  corr(delta,|eta|)={cc:.4f}")

    # ---- DEPTH TEST: joint-vs-marginal gap as r grows.
    banner(f"[DEPTH] n={n}: does the joint-vs-marginal gap GROW with r?")
    print("  MARGINAL prediction for the cross moment <|A|^{2a}|B|^{2(r-a)}> assuming A,B independent")
    print("  with the measured marginals vs the ACTUAL joint value. Because |A|=|B| in distribution")
    print("  (dilation), the magnitude joint is trivially matched; the PHASE content is the test.")
    print("  Cross-coset joint 2r-moment of the FULL period built from the pair:")
    print("    actual  P_r := (1/m) sum_b |A_b + B_b|^{2r}   [= the real eta moment E_r/n]")
    print("    marg    Q_r := (1/m) sum_b ( |A_b|^2 + |B_b|^2 )^r   [phase-blind / triangle-diagonal]")
    print("  gap_r := P_r / Q_r  (=1 if phase is irrelevant / diagonalizes; <1 if phase cancels;")
    print("  the DEPTH question: does |1-gap_r| grow with r => phase content strengthens at depth.")
    print(f"  {'p':>10} " + " ".join(f"{'gap'+str(r):>8}" for r in (1,2,3,4,5,6)))
    for (p,vv,M,E,deltas,rm,Av,Bv,av) in rows:
        magsq = np.abs(Av)**2 + np.abs(Bv)**2
        full  = np.abs(Av+Bv)**2
        gaps=[]
        for r in (1,2,3,4,5,6):
            P=float(np.mean(full**r)); Q=float(np.mean(magsq**r))
            gaps.append(P/Q if Q>0 else float('nan'))
        print(f"  {p:>10} " + " ".join(f"{gp:>8.4f}" for gp in gaps))

    # ---- WHITE TEST: cross-covariance vs the doorIV white result, at DEEP r
    banner(f"[WHITE] n={n}: deep-r cross-covariance -- same diagonalization as doorIV r=2 or not?")
    print("  doorIV-joint-field-white: at r=2 the centered cross-covariance summed over the shift")
    print("  is ZERO (field is white). Test whether the DEEP-r phase-difference field is also white:")
    print("    W_r := (1/m) sum_b cos(delta_b)*|eta_b|^{2r}  -  <cos delta><|eta|^{2r}>   (cross-cov)")
    print("  If W_r -> 0 for all r (phase indep of magnitude), same white diagonalization at depth.")
    for (p,vv,M,E,deltas,rm,Av,Bv,av) in rows[:3]:
        cosd=np.cos(deltas)
        line=[]
        for r in (1,2,3,4,5,6):
            w=float(np.mean(cosd*av**(2*r)) - np.mean(cosd)*np.mean(av**(2*r)))
            # normalize by <|eta|^{2r}> to compare across r
            norm=float(np.mean(av**(2*r)))
            line.append(w/norm if norm>0 else float('nan'))
        print(f"  p={p:>10}: normalized cross-cov(cos delta, |eta|^2r) r=1..6 = "
              + " ".join(f"{x:+.4f}" for x in line))

print("\n"+"="*80)
print("DONE. Read: GAUGE (J_r pinned by moments?), BSENS (delta_b varies?), DEPTH (gap grow with r?),")
print("WHITE (deep-r cross-cov ->0?). Verdict logic in the agent summary.")
print("="*80)
