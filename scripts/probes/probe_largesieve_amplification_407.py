#!/usr/bin/env python3
"""
THE HONEST A-PRIORI AMPLIFIER BOUND (no peeking at b*).

The I-S amplification, written as a genuine theorem, is:
   For ANY choice of amplifier coefficients (a_l), define A(b)=sum_l a_l chibar_l(b). Then for ALL b,
        |A(b)|^2 |T(b)|^2 <= sum_{b'} |A(b')|^2 |T(b')|^2 = m * AmpM(a).
   => |T(b)|^2 <= m*AmpM(a) / |A(b)|^2,  valid for every b with A(b)!=0.
   Taking b=b* (worst): |T(b*)|^2 <= m*AmpM(a)/|A(b*)|^2. To make this a THEOREM you need a LOWER
   bound on |A(b*)|^2 that holds without knowing b*. The only universal lower bound over ALL b is
        min_b |A(b)|^2,  which for any nonconstant A is ~ 0 (A has zeros). 
   => the a-priori bound is  max_b|T|^2 <= m*AmpM(a)/min_b|A(b)|^2 = infinity. USELESS.

   The I-S method ESCAPES this in the automorphic setting because there a_l is chosen so that
   |A(b)|^2 >= L (a constant LOWER bound for ALL b) using HECKE MULTIPLICATIVITY:
        sum_l |lambda_p(f)|^2-type identities give A(b)>= amplifier length for the TARGET spectral
        parameter, uniformly. Here the analogue would need: a positive combination of the characters
        chi_l that is BOUNDED BELOW on all of Q. But sum_l |a_l chibar_l(b)| can't be bounded below
        away from 0 for a SHORT amplifier (l in a set of size L<<m) -- a short character sum has zeros.

   So the I-S route needs a LOWER bound on a short character sum (the amplifier) = the SAME kind of
   incomplete-character-sum control as the original problem. CIRCULAR.

VERIFY: (a) min_b |A(b)|^2 over a short amplifier is ~0 (amplifier has near-zeros), so the honest
bound diverges; (b) the amplified moment AmpM with a generic short amplifier equals the diagonal
||a||^2 (m-1) p (no Hecke gain), so even the FORM of the bound is m*||a||^2 (m-1) p / min|A|^2.
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
    twp=2.0*math.pi/p; omega=cmath.exp(-2j*math.pi/m); jj=np.arange(m)
    eta_=pow(g,m,p); xs=np.array([pow(eta_,i,p) for i in range(n)],dtype=np.int64)
    etavals=np.empty(m,dtype=complex); c=1
    for j in range(m):
        ang=((c*xs)%p)*twp
        etavals[j]=np.cos(ang).sum()+1j*np.sin(ang).sum(); c=c*g%p
    T=m*etavals+1.0; maxT2=(np.abs(T)**2).max()
    B2eta=(np.abs(etavals)**2).max()
    print(f"n={n} p={p} m={m}  B2eta/(n ln m)={B2eta/(n*math.log(m)):.3f}  max|T|^2={maxT2:.3e}")
    for L in [3,10,30,100]:
        if L>=m: continue
        # generic short amplifier: a_l = 1 for l in {1..L}. A(b_j)=sum_{l=1}^L omega^{l j} (Dirichlet kernel)
        A=np.zeros(m,dtype=complex)
        for l in range(1,L+1): A+=omega**(l*jj)
        absA2=np.abs(A)**2
        minA2=absA2.min(); medA2=np.median(absA2); peakA2=absA2.max()
        AmpM=(absA2*np.abs(T)**2).mean()
        diag=L*(m-1)*p
        # honest a-priori bound = m*AmpM/min_b|A|^2:
        honest=m*AmpM/max(minA2,1e-30)
        print(f"    L={L:4d}: min|A|^2={minA2:.2e} med|A|^2={medA2:.1f} peak|A|^2={peakA2:.0f}  AmpM/diag={AmpM/diag:.3f}  HONEST_bound=m*AmpM/min|A|^2 = {honest:.2e}  (true={maxT2:.2e}; ratio={honest/maxT2:.1e})")
    print()

for n,beta in [(16,4),(32,4),(64,4)]:
    run(n,beta)
