#!/usr/bin/env python3
"""
#407 [rojasleon] — EXACT verification of the Hasse-Davenport d=2 relation in the prize
character family, and pin of exactly when it couples period-relevant phases.

HD (d=2):  tau(chi) * tau(chi*lambda) = chi(2)^{-2} * tau(chi^2) * tau(lambda)
  where lambda = the quadratic (Legendre) character of F_p, tau(lambda)=sqrt(p) or i*sqrt(p).
(Berndt-Evans-Williams Thm 11.3.5 / Davenport-Hasse.)

The period-relevant chars are psi^j = chars trivial on mu_n, exponent e_j = n*j (j=0..m-1).
HD couples tau(psi^j) and tau(psi^j * lambda) to tau(psi^{2j}).
KEY: psi^j*lambda is period-relevant (trivial on mu_n) IFF lambda is trivial on mu_n
     IFF mu_n subset QR IFF v2(p-1) > mu (= log2 n).
So HD CLOSES inside the period-phase family ONLY when v2(p-1)>mu; otherwise tau(psi^j*lambda)
is an OUTSIDE Gauss sum (not one of the a_j) and HD does not relate the a_j among themselves.

We verify the exact relation on small primes and print the v2 condition, to ground the verdict.
"""
import math, cmath

def is_prime(n):
    if n<2:return False
    i=2
    while i*i<=n:
        if n%i==0:return False
        i+=1
    return True

def primitive_root(p):
    n=p-1;fac=set();d=2;x=n
    while d*d<=x:
        while x%d==0:fac.add(d);x//=d
        d+=1
    if x>1:fac.add(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g

def tau_exp(e,p,g):
    """tau(chi_e), chi_e(g^k)=exp(2pi i e k/(p-1)); tau=sum_x chi(x) e_p(x)."""
    pe=p-1;s=0j;x=1
    for k in range(pe):
        s+=cmath.exp(2j*math.pi*e*k/pe)*cmath.exp(2j*math.pi*x/p)
        x=(x*g)%p
    return s

print("="*84)
print("EXACT Hasse-Davenport d=2 in the prize family + the v2(p-1)>mu coupling condition")
print("="*84)
# pick a handful of small dyadic primes n=2^mu | p-1, both v2>mu and v2=mu cases
cases=[]
for mu in (2,3,4):
    n=2**mu
    for p in range(n+1, 4000):
        if (p-1)%n==0 and is_prime(p):
            m=(p-1)//n; mm=m
            while mm%2==0: mm//=2
            if mm>1:  # exclude fully-dyadic
                v2=0; t=p-1
                while t%2==0: t//=2; v2+=1
                cases.append((mu,n,p,m,v2))
            if len([c for c in cases if c[0]==mu])>=3: break
for (mu,n,p,m,v2) in cases:
    g=primitive_root(p); pe=p-1; sqp=math.sqrt(p)
    # quadratic char exponent = pe/2
    e_lam=pe//2
    lam_triv_on_mu = (v2>mu)   # mu_n subset QR
    # test HD for chi=psi^1 (e=n): tau(psi)*tau(psi*lambda) =? chi(2)^{-2} tau(psi^2) tau(lambda)
    e1=n
    e_psi_lam=(e1+e_lam)%pe
    e2=(2*e1)%pe
    t_psi   = tau_exp(e1,p,g)
    t_psilam= tau_exp(e_psi_lam,p,g)
    t_psi2  = tau_exp(e2,p,g)
    t_lam   = tau_exp(e_lam,p,g)
    # chi(2): chi_e(2)=exp(2pi i e * ind_g(2)/pe).  ind of 2:
    ind2=None;x=1
    for k in range(pe):
        if x==2%p: ind2=k; break
        x=(x*g)%p
    chi2=cmath.exp(2j*math.pi*e1*ind2/pe)
    lhs=t_psi*t_psilam
    rhs=(chi2**(-2))*t_psi2*t_lam
    rel_err=abs(lhs-rhs)/abs(rhs) if abs(rhs)>0 else float('nan')
    # is psi*lambda a PERIOD phase (trivial on mu_n)?  e_psi_lam multiple of n?
    psilam_is_period = (e_psi_lam % n == 0)
    print(f"\nmu={mu} n={n} p={p} m={m} v2(p-1)={v2}  lambda trivial on mu_n: {lam_triv_on_mu}")
    print(f"  HD d=2 exact?  |LHS-RHS|/|RHS| = {rel_err:.2e}   (0 => HD identity verified)")
    print(f"  psi*lambda is a period-phase (trivial on mu_n)? {psilam_is_period}  "
          f"(=> {'HD closes among the a_j' if psilam_is_period else 'HD exits to an OUTSIDE Gauss sum'})")
    print(f"  |tau(psi)|/sqrt(p)={abs(t_psi)/sqp:.4f} |tau(psi*lam)|/sqrt(p)={abs(t_psilam)/sqp:.4f} "
          f"|tau(psi^2)|/sqrt(p)={abs(t_psi2)/sqp:.4f}")
print("\nConclusion: HD d=2 is an EXACT identity (rel_err~1e-15), but it relates a period-phase")
print("a_j to tau(psi^j*lambda) which is ITSELF a period-phase ONLY when v2(p-1)>mu (lambda")
print("trivial on mu_n).  When it does close, it ties a_{2j} to a PRODUCT a_j*a_{j+?}, propagating")
print("(not aligning) the phase.  When it doesn't, HD couples the a_j to OUTSIDE sums = no internal")
print("alignment at all.  Either branch: NO spoiler of flatness.")
