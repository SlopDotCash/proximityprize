"""
#407 The DEEPER Stickelberger test: the STICKELBERGER CONGRUENCE
(not just valuation) and whether the mod-pi^{s+1} data constrains arg(tau).

Stickelberger congruence (prime field f=1, p):  for 0 <= a <= p-2,
    g(omega^{-a}) / pi^{a}  ==  -1/a!   (mod pi),
where pi is a uniformizer with pi^{p-1} = -p, omega the Teichmuller char.
Equivalently  g(omega^{-a}) == -pi^a / a!  (mod pi^{a+1}).

This is a REAL statement about the Gauss sum value (not just |.|), in the p-adic
metric.  The prior refutation says: this is non-archimedean, the prize is
archimedean, |g|=sqrt p fixes the only archimedean datum.

THE PRESSURE TEST (the thing the prior loop did NOT do explicitly):
  Map the Gauss sum into BOTH completions.  In C: g has |g|=sqrt p and an arg.
  In C_p (p-adic): g has v_p(g)=a/(p-1) and a leading digit -1/a!.
  These are the SAME algebraic number g(omega^{-a}) in Qbar, embedded two ways.
  The arg in C and the digit in C_p are coordinates of ONE algebraic number.
  QUESTION: are they INDEPENDENT (then Stickelberger is archimedean-blind, prior
  refutation correct), or does the algebraicity + the EXACT digit data over-
  determine arg enough to bound the DFT max?

We test by: (A) computing arg(tau_a) in C; (B) computing the Stickelberger
'digit' invariant  d(a) = (-1/a! mod p)  [the residue of g/pi^a, identified with
a residue in F_p];  (C) measuring mutual information / any functional dependence
arg <-> d(a).  If NONE, the refutation is confirmed AND sharpened with a concrete
independence certificate.
"""
import numpy as np, cmath, math
from sympy import primitive_root

def setup(p):
    g = primitive_root(p)
    dlog=[0]*p; x=1
    for k in range(p-1):
        dlog[x]=k; x=(x*g)%p
    w=cmath.exp(2j*math.pi/p)
    def gauss(a):  # tau(omega^{-a}) with omega(g)=zeta_{p-1}; here chi^a(g^k)=zeta^{a k}
        s=0j
        for t in range(1,p):
            s+=cmath.exp(2j*math.pi*(a*dlog[t])/(p-1))*(w**t)
        return s
    return g,dlog,gauss

def stick_digit(a,p):
    # -1/a! mod p  (the Stickelberger leading coefficient residue, f=1)
    fa=1
    for i in range(1,a+1): fa=(fa*i)%p
    inv=pow(fa,p-2,p)
    return (-inv)%p

for p in [73,97,193,257]:
    g,dlog,gauss=setup(p)
    A=p-1
    args=np.array([cmath.phase(gauss(a)) for a in range(1,A)])
    digs=np.array([stick_digit(a,p) for a in range(1,A)])
    # Is arg a function of the digit residue?  Sort by digit, look at arg spread.
    # Pearson between arg and (digit as angle 2pi d/p):
    dang=2*math.pi*digs/p
    # correlation of unit vectors
    cr = np.mean(np.exp(1j*(args-dang)))
    cr2= np.mean(np.exp(1j*(args+dang)))
    # also: does the digit predict the SIGN of Re(tau) or anything coarse?
    mags=np.array([abs(gauss(a)) for a in range(1,A)])
    print(f"p={p:4d}: |tau| mean={mags.mean():.3f} (sqrt p={math.sqrt(p):.3f}), "
          f"|<e^{{i(arg-dang)}}>|={abs(cr):.4f}  |<e^{{i(arg+dang)}}>|={abs(cr2):.4f}")
