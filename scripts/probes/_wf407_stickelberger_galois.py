"""
#407 The Galois/conjugation Stickelberger structure -- the deepest test.

Gauss sums tau(chi^j) for j=0..p-2 are the conjugates of a single algebraic number
under Gal(Q(zeta_{p-1},zeta_p)/Q(zeta_p)) = (Z/(p-1))^*, acting by
   sigma_t : tau(chi^j) |-> tau(chi^{jt})  up to an explicit root of unity (Hasse-Davenport / Galois).
Stickelberger's theorem gives the EXACT prime factorization of the ideal (tau(chi^{-a}))
= P^{S(a)} where S(a)=Stickelberger element = sum_t <a t/(p-1)> sigma_t^{-1}.

KEY NEW QUESTION (beyond the prior loop): The prize DFT sum is
   D(w) = sum_{j in Zm} w^{-j} a_j,  a_j = tau(chi^{j'})/sqrt p  (j over odd index group).
The full vector (a_0,...,a_{m-1}) is a GALOIS ORBIT.  Its DFT is itself (up to the
self-duality noted in the brief) the period vector eta_b.  Stickelberger constrains
the orbit MULTIPLICATIVELY (products = norms = ideals).  Does the orbit's being a
single Galois orbit with KNOWN factorization force a NONTRIVIAL LOWER bound on the
DFT max (anti-flatness), or impose ANY archimedean constraint?

TEST 1 (norm constraint): prod_b eta_b = N(eta) is a rational integer (Galois-stable);
   compute it, compare |N|^{1/m} (geometric mean of |eta_b|) vs the MAX.  The prior
   refutation claim: N lower-bounds the geometric mean ~sqrt n, blind to the max.
   We verify the GAP house/geomean = the conjugate variation, and quantify it.

TEST 2 (the genuinely new probe): Stickelberger says the IDEAL factorization of each
   eta_b (as alg int in Q(zeta_n)) is determined by digit sums.  Two eta_b with the
   SAME ideal factorization differ by a UNIT.  Do the units (which carry ALL the
   archimedean info) have bounded house?  I.e. is the archimedean variation a UNIT
   phenomenon Stickelberger cannot see?  We test: are the |eta_b| (the houses of
   conjugates) explained by their norms (algebraic) or do equal-norm conjugates
   still spread (unit/archimedean)?
"""
import numpy as np, cmath, math
from sympy import primitive_root, factorint
from functools import reduce

def setup(p,n):
    g=primitive_root(p); m=(p-1)//n
    w=cmath.exp(2j*math.pi/p)
    mu_n=[pow(g,m*l,p) for l in range(n)]
    def eta(b): return sum(w**((b*y)%p) for y in mu_n)
    # the conjugate periods: eta_{g^c} for c=0..m-1 are the m Galois conjugates
    # (b ranges over cosets of mu_n in F_p^*; representatives g^c, c=0..m-1).
    reps=[pow(g,c,p) for c in range(m)]
    return m,eta,reps,mu_n,g,w

for (p,n) in [(73,8),(97,16),(193,8),(257,16),(769,8),(1153,16)]:
    if (p-1)%n: continue
    m,eta,reps,mu_n,g,w=setup(p,n)
    conj=np.array([eta(b) for b in reps])     # the m distinct conjugate periods
    mags=np.abs(conj)
    house=mags.max(); gmean=np.exp(np.mean(np.log(mags+1e-30)))
    # algebraic norm = product of conjugates (should be a real integer)
    N=reduce(lambda a,b:a*b, conj, 1+0j)
    print(f"p={p:5d} n={n:3d} m={m:4d}: house={house:7.3f} geomean={gmean:7.3f} "
          f"house/geomean={house/gmean:5.3f}  N=prod(eta)={N.real:+.1f}{N.imag:+.1e}i "
          f"|N|^(1/m)={abs(N)**(1/m):6.3f}")
print()
print("INTERPRETATION: house/geomean is the CONJUGATE VARIATION (the sqrt(log m)")
print("archimedean factor). |N|^(1/m)~geomean~sqrt n is the algebraic/Stickelberger")
print("part. Stickelberger pins N (and ideal fact) but NOT house/geomean.")
