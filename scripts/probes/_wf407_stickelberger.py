"""
#407 Stickelberger / Gross-Koblitz p-adic-digit attack on the prize DFT flatness.

Prize residual (one face): a_j = tau(psi^j)/sqrt(q), j over the ODD group Z/m,
m=(q-1)/n. Prove DFT sup-norm  max_w |sum_j w^{-j} a_j| <= C sqrt(m log m).

Stickelberger angle:  tau(psi^j) has EXACT p-adic valuation given by the base-p
digit sum of the corresponding exponent (Stickelberger's congruence /
Gross-Koblitz).  QUESTION: does the digit-sum structure of the {tau_j} impose a
*usable archimedean* constraint that forces cancellation in the DFT sum, or is the
prior refutation right that it is archimedean-blind?

This probe tests the EXACT mechanism:
  (1) Compute the genuine Gauss sums tau(psi^j) numerically (complex), j in Z/m.
  (2) Compute their Stickelberger data: for psi = omega^{-1} (omega Teichmuller),
      psi^j = omega^{-j}, the relevant exponent is j; the digit sum here (f=1,
      prime field) is trivially controlled, BUT the AUTOMORPHISM structure is the
      point: the conjugates of tau under Gal(Q(zeta_{q-1})/Q) = (Z/(q-1))* permute
      the tau(psi^j) and Stickelberger says sigma_t(tau(psi^j)) relates to
      tau(psi^{jt}) up to roots of unity.
  (3) TEST: is arg(tau_j) determined / constrained by the p-adic (digit) data, or
      is it 'free' (Katz-equidistributed)?  Measure correlation between the
      Stickelberger valuation pattern and arg, and whether ANY digit-based
      reweighting flattens the DFT.
"""
import numpy as np
import cmath, math
from sympy import isprime, primitive_root, factorint

def gauss_sums_subgroup(p, n):
    """Return q=p, m=(p-1)//n, and the array a_j = tau(psi^j)/sqrt(p)
       for j over the index group, plus the periods eta_b.
       psi = additive char x->e_p(x); chi a generator of the order-(p-1) char group.
       We use chi = omega (a fixed multiplicative char of full order p-1)."""
    g = primitive_root(p)
    # discrete log table
    dlog = [0]*p
    x = 1
    for k in range(p-1):
        dlog[x] = k
        x = (x*g) % p
    w = cmath.exp(2j*math.pi/p)            # e_p
    zpm1 = cmath.exp(2j*math.pi/(p-1))     # zeta_{p-1}
    # multiplicative char chi^a (a) : chi^a(g^k) = zeta_{p-1}^{a k}
    def gauss(a):
        # tau(chi^a) = sum_{t in F_p^*} chi^a(t) e_p(t)
        s = 0j
        for t in range(1, p):
            k = dlog[t]
            s += cmath.exp(2j*math.pi*(a*k)/(p-1)) * (w**t)
        return s
    m = (p-1)//n
    # the index group for the subgroup mu_n sums: characters of order dividing n
    # are chi^{m*i}; the DFT face uses a_j = tau(chi^?)... we follow the synthesis:
    # eta_b = sum_{y in mu_n} e_p(b y); mu_n = {g^{m*l}: l=0..n-1}
    mu_n = [pow(g, m*l, p) for l in range(n)]
    def eta(b):
        return sum(w**((b*y) % p) for y in mu_n)
    return p, m, g, dlog, gauss, eta, mu_n

def report(p, n):
    q, m, g, dlog, gauss, eta, mu_n = gauss_sums_subgroup(p, n)
    # the periods eta_b, b != 0
    etas = np.array([eta(b) for b in range(1, p)])
    M = np.max(np.abs(etas))
    base = math.sqrt(n*math.log(max(m,2)))
    # Gauss sums of the characters TRIVIAL on mu_n: chi^{?}. The non-principal
    # characters that are nontrivial give |tau|=sqrt p.
    # The DFT-flatness face: a_i = tau(chi^i)/sqrt q for chi of order m? Let's
    # directly compute the m characters of order dividing m? Actually the relevant
    # set is characters chi^i, i=0..p-2; |tau|=sqrt p for i!=0.
    return q, m, M, base, M/base, etas, gauss, g, dlog

for (p,n) in [(73,8),(97,16),(193,8),(257,16),(769,8),(1153,16),(3329,256)]:
    if (p-1)%n!=0: 
        print(p,n,"skip (n not | p-1)"); continue
    q,m,M,base,ratio,etas,gauss,g,dlog = report(p,n)
    print(f"p={p:5d} n={n:3d} m={m:5d}  M={M:8.3f}  sqrt(n ln m)={base:7.3f}  M/base={ratio:.3f}")
