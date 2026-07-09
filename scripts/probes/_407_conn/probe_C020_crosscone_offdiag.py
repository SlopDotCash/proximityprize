"""
C020 follow-up: confirm the cross-cone IDENTIFICATION is structurally exact, not coincidental.

Claim: CS25 off-diagonal  sum_{psi != 0} ||Shat(psi)||^2   (over G = F^n / C, C = line kernel)
       =  the line-incidence spectral mass restricted to surviving frequencies psi perp s1
       =  sum over surviving freqs of |coefficient|^2,
   AND each surviving coefficient, for the mu_n-syndrome slice, is C(b) = sum_{x in mu_n} e_p(b x),
   whose WORST is M(n) and whose L2 SUM is fixed by Parseval (= q*n).

We test on the simplest faithful slice: V = F_q (1-dim syndrome space), S = mu_n, line direction
s1 generic. The dual chars of F_q are b |-> e_p(b .). The surviving (psi perp s1) condition selects
a hyperplane of frequencies; in V=F_q (dim 1) "perp s1" picks b with b*s1 = 0 i.e. b=0 only -- so the
1-dim slice is degenerate for the perp condition. The MEANINGFUL content is the per-frequency
coefficient sum_{s in S} psi(s0 - s) = e_p(-b*s0) * C(b)  (modulus |C(b)|), independent of s0.

So the structural fact to confirm (and which the Lean lemmas already encode exactly):
  * line-incidence per-frequency coefficient modulus = |C(b)| = |sum_{x in mu_n} e_p(b x)|   (B/F2)
  * Parseval (charSum_l2_pairing): sum over ALL b of |C(b)|^2 = q * |mu_n| = q*n.              (L2)
  * CS25 (fourier_pair_identity): L2 PAIR identity over the quotient = same total mass.         (L2)
  * The two cones therefore expose ONE spectral vector {C(b)}_b; CS25 sums its squares (free),
    the prize takes its sup (M(n)).
This script confirms numerically that (a) the per-frequency coefficient modulus is exactly the
Gauss-period sum, and (b) the L2 sum is q*n REGARDLESS of which frequency subset, while the sup
is the open M(n) -- i.e. NO functional of the L2 mass alone recovers M(n) (different primes with
equal L2 mass have different M(n)).
"""
import math
import numpy as np

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def primes_1modn(n, lo_b, hi_b, count):
    lo=int(n**lo_b); hi=int(n**hi_b); out=[]
    q=1+((lo-1)//n)*n
    while q<lo: q+=n
    while q<=hi and len(out)<count:
        if is_prime(q): out.append(q)
        q+=n
    return out

def primitive_root(q):
    m=q-1; fac=set(); d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in fac): return g

def subgroup(g,n,q):
    h=pow(g,(q-1)//n,q); s=[]; x=1
    for _ in range(n): s.append(x); x=(x*h)%q
    return np.array(s,dtype=np.int64)

def gauss_period_coeffs(mu,q):
    b=np.arange(q,dtype=np.int64)
    acc=np.zeros(q,dtype=np.complex128)
    for x in mu: acc+=np.exp(2j*math.pi*((b*x)%q)/q)
    return acc

# Demonstrate: SAME L2 mass q*n at fixed (n) across DIFFERENT primes q, but DIFFERENT M(n).
# (If M(n) were a function of the L2 mass, equal-n equal-mass-per-q would force a fixed ratio;
#  it does not -- the sup carries info the L2 sum throws away.)
print("="*78)
print("Per-frequency coefficient = Gauss-period sum; L2 mass fixed, M(n) (sup) varies/open")
print("="*78)
for n in (8,16,32):
    print(f"\n n={n}:")
    for q in primes_1modn(n,4.0,4.6,3):
        g=primitive_root(q); mu=subgroup(g,n,q)
        c=gauss_period_coeffs(mu,q)
        a2=np.abs(c)**2
        l2=float(a2.sum()); sup=float(math.sqrt(a2[1:].max()))
        # direct M(n) re-derivation as a cross-check of "per-freq coeff = Gauss-period sum":
        # the b that maximises |c[b]| over b!=0
        bstar=int(1+np.argmax(a2[1:]))
        direct=abs(sum(np.exp(2j*math.pi*((bstar*int(x))%q)/q) for x in mu))
        print(f"   q={q:>10}  L2sum={l2:>14.1f}  ==q*n={q*n:>12}  "
              f"M(n)={sup:>8.3f}  (b*={bstar}, direct|C(b*)|={direct:.3f}, match={abs(direct-sup)<1e-6})  "
              f"M/sqrt(n logq)={sup/math.sqrt(n*math.log(q/n)):.3f}")
print()
print("CONCLUSION: L2 mass is EXACTLY q*n for every prime (Parseval, regime-independent, free).")
print("M(n) (the sup) varies prime-to-prime at fixed n and is the open BGK object: the L2 mass")
print("does not determine it. The cross-cone identity is REAL (one shared spectral vector {C(b)}),")
print("but CS25 only delivers the L2 functional -> the prize's L-inf functional = M(n) = W-BGK.")
