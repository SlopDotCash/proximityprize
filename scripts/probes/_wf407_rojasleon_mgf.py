#!/usr/bin/env python3
"""
#407 route [rojasleon]: Rojas-Leon independence -> MGF factorization (numpy-vectorized).

Q1  MGF / sub-Gaussian test of the phase trig-poly  P(c)=sum_{j=1}^{m-1} a_j e(-jc/m),
    a_j = tau(psi^j)/sqrt(p) unimodular.  If the m-1 phases were jointly INDEPENDENT
    unimodular, ||P||_inf <= sqrt(2 (m-1) log(m-1)) (Chernoff+union over m roots).
    We measure ||P||_inf and B and compare to the random-flat law.

Q2  HASSE-DAVENPORT alignment.  The ONLY relations (Rojas-Leon 2207.12439) are
    conjugation tau(chi)tau(chibar)=chi(-1)q, Galois tau(chi^p)=tau(chi), and HD
    prod_{eps^d=1} tau(chi*eps) = chi(d)^{-d} tau(chi^d) (HD const).  For d=2 this
    deterministically couples a_{2j} to a_j and a_{j+m/2}.  We test whether that
    coupling is a CONSTANT phase (=> alignment, potential spoiler of flatness) and
    whether it inflates ||P||_inf above the phase-shuffled control.
"""
import math, cmath
import numpy as np
np.random.seed(20260613)

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def primitive_root(p):
    n=p-1; fac=set(); d=2
    while d*d<=n:
        while n%d==0: fac.add(d); n//=d
        d+=1
    if n>1: fac.add(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    raise RuntimeError

def find_prime(n, beta, maxp=4_000_000):
    target=int(round(n**beta))
    t0=max(2,target//n)
    for dt in range(0,400000):
        for t in (t0+dt,t0-dt):
            if t<2: continue
            p=1+n*t
            if p<=n or p>maxp: continue
            if is_prime(p):
                m=(p-1)//n; mm=m
                while mm%2==0: mm//=2
                if mm>1: return p
    return None

def all_gauss_sums(p, g):
    """Return tau[e] for e=0..p-2 where chi_e(g^k)=exp(2pi i e k/(p-1)).
       tau(chi_e)=sum_{k=0}^{p-2} exp(2pi i e k/(p-1)) e_p(g^k).
       Vectorized: tau = F @ w where F[e,k]=exp(2pi i e k/(p-1)), w[k]=e_p(g^k).
       That's the DFT of w over index k -> use np.fft.fft (length p-1)."""
    pe=p-1
    gk=np.empty(pe,dtype=np.int64)
    x=1
    for k in range(pe):
        gk[k]=x; x=(x*g)%p
    w=np.exp(2j*np.pi*gk/p)               # e_p(g^k)
    tau=np.fft.fft(w)                      # tau[e]=sum_k w[k] exp(2pi i e k/pe)  (note fft sign +)
    # np.fft.fft uses exp(-2pi i ...); we want +. Use ifft*pe or conj trick:
    tau=np.fft.ifft(w)*pe                  # ifft gives (1/pe) sum w[k] exp(+2pi i e k/pe)
    return tau                             # tau[e], e=0..pe-1, |tau|~sqrt(p) for e!=0

def run(n, beta):
    p=find_prime(n,beta)
    if p is None: return None
    g=primitive_root(p)
    m=(p-1)//n
    pe=p-1; sqp=math.sqrt(p)
    tau=all_gauss_sums(p,g)
    # chars trivial on mu_n have exponent e = n*j, j=0..m-1.  a_j = tau(psi^j)/sqp
    idx=(n*np.arange(0,m))%pe
    A=tau[idx]/sqp                         # A[0]=tau(triv)/sqp = -1/sqp; A[1..m-1] unimodular
    a=A[1:]                                # j=1..m-1
    # periods eta_c = (1/m)[ -1 + sum_{j=1}^{m-1} tau(psi^j) e(-jc/m) ]  (inverse DFT)
    #            = (1/m) sum_{j=0}^{m-1} tau(psi^j) e(-jc/m)   with tau(psi^0)=-1
    full=tau[idx].copy()                   # length m, full[0] = tau(trivial char)= -1
    # eta_c = (1/m) * IDFT_m(full) evaluated... eta_c = (1/m) sum_j full[j] e(-2pi i j c/m)
    eta=np.fft.fft(full)/m                 # fft: sum_j full[j] exp(-2pi i j c /m) -> matches
    B=float(np.max(np.abs(eta)))
    rms=float(np.sqrt(np.mean(np.abs(eta)**2)))
    # phase trig poly P(c)=sum_{j=1}^{m-1} a_j e(-jc/m):
    padded=np.zeros(m,dtype=complex); padded[1:]=a
    P=np.fft.fft(padded)                   # P[c]=sum_j padded[j] exp(-2pi i j c/m)
    supP=float(np.max(np.abs(P)))
    return dict(p=p,m=m,g=g,sqp=sqp,a=a,A=A,B=B,rms=rms,eta=eta,supP=supP,tau=tau,idx=idx)

print("="*92)
print("ROUTE rojasleon: Rojas-Leon independence -> MGF factorization + Hasse-Davenport spoiler")
print("="*92)
for (n,beta) in [(8,4),(16,4),(8,5),(16,5),(32,4),(64,3.5),(32,5),(64,4)]:
    R=run(n,beta)
    if R is None:
        print(f"n={n} beta={beta}: no prime in range"); continue
    m=R['m']; a=R['a']; supP=R['supP']; B=R['B']; sqp=R['sqp']
    L=m-1
    rand_law=math.sqrt(L*math.log(L)) if L>1 else 1.0
    ub_law=math.sqrt(2*L*math.log(L)) if L>1 else 1.0
    moddev=float(np.max(np.abs(np.abs(a)-1.0)))
    print(f"\n--- n={n} beta={beta}  p={R['p']}  m={m}  log2(m)={math.log2(m):.1f} ---")
    print(f"  B={B:.4f}  rms={R['rms']:.4f}(=sqrt(n)?{math.sqrt(n):.4f})  "
          f"B/sqrt(n)={B/math.sqrt(n):.3f}  B/sqrt(n ln m)={B/math.sqrt(n*math.log(m)):.3f}")
    print(f"  |a_j| maxdev from 1 = {moddev:.1e}    (unimodular phases, energy={np.sum(np.abs(a)**2):.1f}~{L})")
    print(f"  ||P||_inf={supP:.3f}   sqrt(L ln L)={rand_law:.3f} (ratio {supP/rand_law:.3f})   "
          f"||P||/sqrt(2L ln L)={supP/ub_law:.3f}  <-- random union-bound saturation")
    # ---- Q2 Hasse-Davenport d=2 ----
    if m%2==0:
        # HD couples a_{2j} <-> a_j * a_{j+m/2}.  Build the phase ratio.
        j=np.arange(1,m)
        idx2=(2*j)%m
        jh=(j+m//2)%m
        good=(idx2!=0)&(jh!=0)
        # a is indexed by j-1 for j in 1..m-1; a[k]=a_{k+1}
        def aval(ix):
            return np.where(ix>=1, R['A'][ix], np.nan)  # A[0]=triv, A[k]=a_k for k>=1
        num=aval(idx2[good])
        den=aval(j[good])*aval(jh[good])
        ratio=num/den
        unit=ratio/np.abs(ratio)
        align=abs(np.nanmean(unit))     # 1 => constant HD phase (deterministic alignment)
        # spoiler test: phase-shuffled control
        ctrl=[]
        for _ in range(30):
            ap=a.copy(); np.random.shuffle(ap)
            pad=np.zeros(m,dtype=complex); pad[1:]=ap
            ctrl.append(np.max(np.abs(np.fft.fft(pad))))
        cmean=float(np.mean(ctrl)); cstd=float(np.std(ctrl))
        print(f"  [HD d=2] |mean unit phase of a_2j/(a_j a_(j+m/2))| = {align:.3f}  "
              f"(1=constant HD alignment, 0=random)   #pairs={int(good.sum())}")
        print(f"  [HD spoiler] ||P||_real={supP:.3f}  vs phase-shuffled ctrl {cmean:.3f}+-{cstd:.3f}  "
              f"inflation={supP/cmean:.3f}  (>1 => structure raises floor)")
print("\nReading: ratio(||P||/sqrt(L lnL))~1 and inflation~1 => phases random-like, NO HD spoiler;")
print("         inflation>>1 => HD alignment genuinely inflates the sup-norm above random.")
