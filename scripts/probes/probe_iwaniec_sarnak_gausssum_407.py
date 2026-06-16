#!/usr/bin/env python3
"""
CLEAN Iwaniec-Sarnak amplification check.

Object: c_k := tau(chi_k), k=1..m-1, |c_k|=sqrt(p). The trig poly is
   T(b) = sum_{k=1}^{m-1} chibar_k(b) c_k = m*eta_b + 1   (over cosets b indexed by j=0..m-1).
We want max_b |T(b)|^2 ~ m^2 * B2 / ... actually m*eta = T-1, so max|T| = m*B + O(1).

L2 (Parseval over the m cosets, exact orthogonality):
   (1/m) sum_{j=0}^{m-1} |T(b_j)|^2 = sum_{k=1}^{m-1} |c_k|^2 = (m-1) p.   [= L2 average]
So avg |T|^2 = (m-1)p ~ m p, i.e. avg|eta|^2 ~ p/m = n. (consistent: RMS eta = sqrt n). GOOD.

AMPLIFIED 2nd moment (Iwaniec-Sarnak): introduce amplifier A(b)=sum_{l in J0} a_l chibar_l(b).
   AmpM := (1/m) sum_j |A(b_j)|^2 |T(b_j)|^2.
Open the squares; orthogonality over the FULL group (1/m)sum_j chibar_i(b_j)chi_{i'}(b_j)=[i=i']:
   AmpM = sum_{k,k', l,l' : k+l = k'+l' (mod m)} a_l abar_{l'} c_k cbar_{k'}.
The constraint k - k' = l' - l ties the Gauss-sum indices to the amplifier indices. The DIAGONAL
(k=k', l=l') gives ||a||^2 * sum_k|c_k|^2 = ||a||^2 (m-1)p. The OFF-diagonal (k!=k') is where Hecke/
Jacobi relations among c_k could create cancellation OR coherence.

The honest question: does the off-diagonal in AmpM REDUCE the amplified moment (so that a cleverly
chosen amplifier makes AmpM/||A||^2_{at b*} small => bound the max)? Compute AmpM exactly, split
diagonal/offdiagonal, and the resulting MAX bound  max_b|T|^2 <= AmpM / |A(b*)|^2.
"""
import math, numpy as np, cmath
def is_prime(n):
    if n<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0:return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True
def odd_part(x):
    while x%2==0:x//=2
    return x
def primitive_root(p):
    phi=p-1;facs=[];mm=phi;d=2
    while d*d<=mm:
        if mm%d==0:
            facs.append(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:facs.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs):return g
def find_prime(n,beta,idx=0):
    target=int(round(n**beta));base=target-(target%n)+1;p=base;cnt=0
    while True:
        if p>3 and p%n==1 and is_prime(p) and odd_part((p-1)//n)>1:
            if cnt==idx:return p
            cnt+=1
        p+=n

def run(n,beta):
    p=find_prime(n,beta); g=primitive_root(p); m=(p-1)//n
    twp=2.0*math.pi/p
    eta_=pow(g,m,p); xs=np.array([pow(eta_,i,p) for i in range(n)],dtype=np.int64)
    etavals=np.empty(m,dtype=complex); c=1
    for j in range(m):
        ang=((c*xs)%p)*twp
        etavals[j]=np.cos(ang).sum()+1j*np.sin(ang).sum()
        c=c*g%p
    T = m*etavals + 1.0                  # T(b_j), j=0..m-1
    B2eta=(np.abs(etavals)**2).max()
    maxT2=(np.abs(T)**2).max()
    jstar=int(np.argmax(np.abs(T)))
    # amplifier A(b_j)=sum_{l=1}^{L} omega^{-l j}; choose L and evaluate
    omega=cmath.exp(-2j*math.pi/m); jj=np.arange(m)
    print(f"n={n} p={p} m={m}  max|T|^2={maxT2:.3e}  jstar={jstar}  B2eta={B2eta:.1f}  B2eta/(n ln m)={B2eta/(n*math.log(m)):.3f}")
    print(f"  L2 avg |T|^2 = (m-1)p = {(m-1)*p:.3e}  (Parseval check: {(np.abs(T)**2).mean():.3e})")
    for L in [1,5,20,50]:
        if L>=m: continue
        A=np.zeros(m,dtype=complex)
        for l in range(1,L+1):
            A+=omega**(l*jj)
        AmpM=(np.abs(A)**2 * np.abs(T)**2).mean()   # (1/m) sum_j
        # bound on the max: max_b|T|^2 <= AmpM / |A(b*)|^2  IF b* in support... but b* is where |A| may be small!
        Abstar2=np.abs(A[jstar])**2
        # the HONEST a-priori bound uses min over b of... no: we must LOWER bound |A(b*)|. Worst case A(b*)~0.
        # The I-S trick needs |A(b*)|^2 >= L^2/2 (amplifier peaks at b*). For a BLIND amplifier we can't aim.
        # Best blind bound: max_b |T(b)|^2 <= AmpM / (min_b |A(b)|^2) -- but min|A|~0. Useless.
        # The REAL I-S: a_l = chi_l(b*) (aim AT b*), then |A(b*)|=L, AmpM gets the diagonal ||a||^2(m-1)p=L(m-1)p.
        a_aim = np.array([np.conj(omega**(l*jstar)) for l in range(1,L+1)])  # a_l = chi_l(b*) to make A(b*)=L
        Aaim=np.zeros(m,dtype=complex)
        for idx,l in enumerate(range(1,L+1)):
            Aaim += a_aim[idx]*omega**(l*jj)
        AmpMaim=(np.abs(Aaim)**2 * np.abs(T)**2).mean()
        boundaim=AmpMaim/np.abs(Aaim[jstar])**2   # |Aaim(b*)|=L => /L^2
        diag=(np.abs(a_aim)**2).sum()*(m-1)*p      # L*(m-1)p
        print(f"    L={L:3d}: AmpM(aim)={AmpMaim:.3e}  diag=L(m-1)p={diag:.3e}  off/diag={AmpMaim/diag-1:+.3f}  |Aaim(b*)|^2={np.abs(Aaim[jstar])**2:.1f}  bound(max|T|^2)={boundaim:.3e}  bound/true={boundaim/maxT2:.2f}")
    print()

for n,beta in [(16,4),(32,4),(64,4)]:
    run(n,beta)
