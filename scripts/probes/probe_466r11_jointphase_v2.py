#!/usr/bin/env python3
"""
probe_466r11_jointphase_v2.py -- LANE J deep interrogation of the two artifacts found in v1:

  ARTIFACT 1: J_2 = <cos 2*delta_b> = 1.0000 EXACTLY at every prime. This forces delta_b in {0,pi},
              i.e. A_b and B_b are COLLINEAR (real ratio) for every coset b. Confirm and explain:
              is this the doorIV coset-half coherence rho=1 result (A,B same ray)?

  ARTIFACT 2: The DEPTH gap_r = P_r/Q_r GROWS with r (1.55, 2.75, 5.25, ...). The make-or-break
              question: is this gap a FUNCTION OF THE MARGINAL MAGNITUDES {|A_b|,|B_b|} alone
              (=> GAUGE, phase content is fake / determined), or does it carry independent phase
              info? Because delta in {0,pi}, the ONLY phase content is the SIGN s_b = +-1 of the
              collinear ratio (same-ray vs opposite-ray). Test whether s_b is:
                (a) a deterministic function of the magnitudes (gauge), or
                (b) genuinely independent b-sensitive bit not seen by moments.

  KEY TEST (gauge-vs-crack): the full period is |A_b + B_b|^2. With A,B collinear:
     |A+B|^2 = (|A| + s_b|B|)^2  where s_b = +-1.
  If s_b = +1 always (same ray), then |A+B| = |A|+|B| is a MAGNITUDE-ONLY function => full GAUGE:
     the joint reduces to marginals, the "phase field" is a constant +1, dead.
  If s_b varies, then the SIGN field is the joint content. We then test: is the sign field
     (i) b-summed count-neutral (Meta-Theorem b-blind) and (ii) a function of |eta| (gauge)?

  Regime: same as v1. >=2 primes, distinct v2. n=8,16 (and n=32 spot check for depth trend).
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
def _pf(n):
    f=set();d=2;m=n
    while d*d<=m:
        if m%d==0:
            f.add(d)
            while m%d==0:m//=d
        d+=1
    if m>1:f.add(m)
    return f
def find_primes(n,beta=4,count=6):
    out=[];p=(n**beta)//n*n+1;need=v2(n)
    while len(out)<count:
        if p>n and isprime(p) and (p-1)%n==0 and v2(p-1)>=need:
            g=primroot(p);h=pow(g,(p-1)//n,p)
            if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in _pf(n)):
                out.append(p)
        p+=n
    return out
def subgroup(p,n,g=None):
    if g is None:g=primroot(p)
    h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)],g,h
def eta_over_cosets(p,S,g):
    m=(p-1)//len(S);Sarr=np.array(S,dtype=np.int64)
    breps=np.empty(m,dtype=np.int64);b=1
    for i in range(m):breps[i]=b;b=(b*g)%p
    tp=2*np.pi/p;re=np.empty(m);im=np.empty(m)
    CH=max(1,4_000_000//max(1,len(Sarr)))
    for lo in range(0,m,CH):
        hi=min(m,lo+CH)
        ph=tp*((breps[lo:hi,None]*Sarr[None,:])%p)
        re[lo:hi]=np.cos(ph).sum(1);im[lo:hi]=np.sin(ph).sum(1)
    return re+1j*im,breps

def banner(s):print("\n"+"="*80+"\n"+s+"\n"+"="*80)

print("probe_466r11_jointphase_v2.py -- deep interrogation of the collinearity + depth-gap artifacts")

for n in (8,16,32):
    beta=4
    primes=find_primes(n,beta=beta,count=6)
    banner(f"n={n}  primes={primes}  v2={[v2(p-1) for p in primes]}")
    for p in primes:
        S,g,h=subgroup(p,n)
        eta,breps=eta_over_cosets(p,S,g)
        av=np.abs(eta)
        m=(p-1)//n
        zeta=h
        Hlow=[pow(h,2*i,p) for i in range(n//2)]
        tp=2*np.pi/p
        # half periods per coset
        A=np.empty(m,dtype=complex);B=np.empty(m,dtype=complex)
        Hl=np.array(Hlow,dtype=np.int64)
        for i in range(m):
            b=int(breps[i]);zb=(zeta*b)%p
            A[i]=np.exp(1j*tp*((b*Hl)%p)).sum()
            B[i]=np.exp(1j*tp*((zb*Hl)%p)).sum()
        # ARTIFACT 1: collinearity. delta = arg(B)-arg(A). test |sin delta| max.
        delta=np.angle(B)-np.angle(A)
        sin_max=float(np.max(np.abs(np.sin(delta))))
        # collinear sign s_b: sign of Re(B * conj(A)) (projection of B onto A ray)
        proj=(B*np.conj(A)).real
        s=np.sign(proj)
        frac_same=float(np.mean(s>0))
        # ARTIFACT 2: is |A+B|^2 a function of (|A|,|B|)? With collinearity |A+B|=| |A| + s|B| |
        aA=np.abs(A);aB=np.abs(B)
        pred_same = (aA+aB)                     # if s=+1 everywhere
        pred_signed = np.abs(aA + s*aB)         # using the measured sign
        actual = np.abs(A+B)
        err_same=float(np.max(np.abs(pred_same-actual)))
        err_signed=float(np.max(np.abs(pred_signed-actual)))
        # GAUGE of the sign field: is s_b a function of |eta_b| (=aA+... )? corr, and does s vary?
        # b-summed content of the sign field (what a b-blind method sees):
        # E_r built two ways: with true signs vs with all +1 (phase-blind same-ray)
        def Emom(vals,r): return float(np.mean(vals**(2*r)))
        # actual full eta = A+B; |eta|=actual. same-ray surrogate magnitude = aA+aB.
        line=[]
        for r in (1,2,3,4,5,6):
            Pr=Emom(actual,r); SR=Emom(pred_same,r)
            line.append(Pr/SR if SR>0 else float('nan'))
        # is the sign bit b-sensitive beyond magnitude? corr(s, aA-aB) and corr(s,av)
        cc_av=float(np.corrcoef(s,av)[0,1]) if np.std(s)>0 else float('nan')
        print(f"  p={p:>10} v2={v2(p-1)}: |sin delta|max={sin_max:.2e} (collinear if ~0)"
              f"  frac(s=+1)={frac_same:.4f}")
        print(f"      |A+B| vs (|A|+|B|): errSame={err_same:.3f}  vs signed:err={err_signed:.2e}"
              f"  corr(s,|eta|)={cc_av:+.3f}")
        print(f"      P_r/SameRay_r (r=1..6): "+" ".join(f"{x:.4f}" for x in line))

print("\n"+"="*80)
print("READ: if |sin delta|~0 => A,B collinear (only a SIGN bit of phase). If frac(s=+1)=1 =>")
print("|A+B|=|A|+|B| pure magnitude => FULL GAUGE (v1 depth-gap was the trivial (|A|+|B|)^2 vs")
print("|A|^2+|B|^2 magnitude inequality, NO phase content). If frac(s=+1)!=1, the sign field is the")
print("only joint content: test its b-sensitivity (corr with |eta|) and whether P_r/SameRay ->1")
print("(sign washes out at depth) or deviates (sign carries deep info).")
print("="*80)
