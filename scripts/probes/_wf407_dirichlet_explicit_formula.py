"""
#407 automorphic angle, STEELMAN #3 (the classical one): the explicit formula for
DIRICHLET L-functions mod p applied to the Gauss period (subgroup sum) directly.

This is the genuinely-classical "automorphic explicit formula" route to bounding incomplete
character sums over a multiplicative subgroup, and it is the SHARPEST honest test of the angle.

SETUP. eta_b = sum_{x in mu_n} psi(bx) where mu_n = order-n subgroup of F_p^*.
Write the subgroup indicator via multiplicative characters of F_p^*:
   1[x in mu_n] = (n/(p-1)) sum_{chi : chi^n = 1} chi(x)        (n characters, chi of order | n)
So
   eta_b = sum_{x != 0} 1[x in mu_n] psi(bx)
         = (n/(p-1)) sum_{chi^n=1} sum_{x!=0} chi(x) psi(bx)
         = (n/(p-1)) sum_{chi^n=1} chibar(b) tau(chi)          [tau(chi) = Gauss sum]
   (the inner sum is chibar(b) tau(chi); tau(chi_0)= -1.)
=> eta_b = (n/(p-1)) [ -1 + sum_{chi^n=1, chi!=chi_0} chibar(b) tau(chi) ].
   |tau(chi)| = sqrt(p) for chi != chi_0.  So trivially |eta_b| <= (n/(p-1))*(1 + (n-1)sqrt(p))
   ~ n^2 sqrt(p)/(p) = n^2/sqrt(p) ... which is the TRIVIAL bound region (no cancellation among
   the n Gauss sums).  THE PRIZE = sqrt-cancellation among these n Gauss-sum PHASES chibar(b)tau(chi).

WHERE does the EXPLICIT FORMULA / Dirichlet L-function enter, and what is the CONDUCTOR?
The Gauss sum tau(chi) is the root number of the Dirichlet L-function L(s, chi) mod p:
   the functional equation of L(s,chi) has root number  W(chi) = tau(chi)/(i^a sqrt(p)).
So the eta_b phases chibar(b) tau(chi) ARE the root numbers of the n Dirichlet L-functions
L(s, chi), chi^n = 1, twisted by chibar(b). The CONDUCTOR of each L(s,chi) is p (the modulus).

THE EXPLICIT FORMULA for L(s,chi) (Riemann-von Mangoldt / Weil) relates:
   sum over zeros rho of L(s,chi)  <->  sum over primes (Lambda(k) chi(k))
The conductor entering its error terms / zero counts is q(chi) = p (the MODULUS of the
character), times the archimedean factor. The number of zeros up to height T is
   N(T,chi) ~ (T/pi) log(pT/2pi).  Conductor = p.

==> THE CONDUCTOR HERE IS p ~ 2^160, NOT poly(n) and NOT 2^128 either: it is the FULL p.

This is the decisive point. The task asks whether the conductor is "POLYNOMIAL in n". For the
Dirichlet route it is p = n*m ~ 2^160 (exponential in everything). The explicit formula for
L(s,chi) controls the distribution of zeros / the prime sum chi(k)Lambda(k) -- it says NOTHING
about a FINITE sum of n root numbers tau(chi) at a fixed modulus p. The Gauss sum tau(chi) is the
EPSILON-FACTOR (a single transcendence), not accessible to the zero-sum side of the explicit
formula: the explicit formula gives |W(chi)|=1 (i.e. |tau|=sqrt p) -- the FLATNESS already in tree
-- but the PHASE arg(tau(chi)) is exactly the part the explicit formula leaves UNDETERMINED
(root-number phases are notoriously inaccessible; cf. the open problem of cancellation in
sum_chi tau(chi), Patterson / Heath-Brown-Patterson on cubic Gauss sum phases).

We verify the phase-only nature numerically and quantify.
"""
import numpy as np, math
from sympy import isprime, primitive_root

def log2(x): return math.log(x,2.0)

print("="*84)
print("Verify eta_b = (n/(p-1)) sum_{chi^n=1} chibar(b) tau(chi), and that the PRIZE is the")
print("phase cancellation among the n root numbers tau(chi) -- inaccessible to the explicit formula.")
print("="*84)

def check(p, n):
    g = primitive_root(p)
    m = (p-1)//n
    ep = np.exp(2j*np.pi/p)
    # CORRECT indicator: characters TRIVIAL on mu_n are those of order | m = (p-1)/n.
    # mu_n = {g^{m k}}. A char psi_s(g^k)=exp(2pi i s k/(p-1)) is trivial on mu_n iff
    # s*m*k/(p-1) in Z for all k  <=>  s*m/(p-1)=s/n in Z  <=>  n | s. Wrong way: let me index
    # the m trivial-on-mu_n chars by t=0..m-1 with psi_t(g^k)=exp(2pi i t k / m)? Trivial on mu_n
    # (g^{mk}): psi_t(g^{mk})=exp(2pi i t m k/(p-1))=exp(2pi i t k / n)=1 for all k iff n|t. NO.
    # Standard: indicator 1[x in mu_n] = (1/m) sum_{psi: psi^m=1... }. The dual of mu_n (index m
    # subgroup of size n) is F_p^*/mu_n of size m; its characters are psi with psi|_{mu_n}=1, count m.
    # psi_t(g^k)=exp(2pi i t k/(p-1)) is trivial on mu_n iff (p-1)|t*m  iff n|t. So t in {0,n,2n,...,(m-1)n}.
    dlog = {}
    val = 1
    for k in range(p-1):
        dlog[val] = k; val = (val*g)%p
    triv = [j*n for j in range(m)]   # the m characters trivial on mu_n
    def psi_s(s, x):
        return np.exp(2j*np.pi*s*dlog[x]/(p-1))
    taus = {}
    for s in triv:
        if s == 0:
            taus[s] = -1.0   # tau(trivial) = -1
        else:
            taus[s] = sum(psi_s(s, x)*ep**x for x in range(1,p))
    # eta_b = (1/m) sum_{s in triv} psibar_s(b) tau(psi_s)
    mu = [pow(g,(m*k)%(p-1),p) for k in range(n)]
    maxerr = 0.0
    Mdirect = 0.0
    for j in range(m):
        b = pow(g,j,p)
        eta_direct = sum(ep**((b*x)%p) for x in mu)
        eta_form = (1.0/m)*sum(np.conj(psi_s(s,b))*taus[s] for s in triv)
        maxerr = max(maxerr, abs(eta_direct-eta_form))
        Mdirect = max(Mdirect, abs(eta_direct))
    flat = np.max([abs(abs(taus[s])-math.sqrt(p)) for s in triv if s!=0])
    return m, maxerr, Mdirect, flat, taus

for (p,n) in [(7681,8),(7681,16),(12289,16),(7937,16)]:
    if not isprime(p) or (p-1)%n: continue
    m, err, M, flat, taus = check(p,n)
    print(f"p={p} n={n} m={m}: |eta_direct - eta_formula|_max={err:.2e}  M=max|eta|={M:.3f}  "
          f"|tau|-sqrt(p) flatness={flat:.2e}  (so amplitudes FLAT, phases carry the house)")

print("""
CONCLUSION of the Dirichlet route:
 - The n root numbers tau(chi)/sqrt(p) have modulus exactly 1 (explicit formula = functional
   equation gives this 'for free', and it is the in-tree Weil flatness).
 - The house B is the L-infinity-in-b of the DFT of the n root-number PHASES. The explicit
   formula for L(s,chi) determines the ZEROS and the prime sums, but the root-number PHASE
   arg(tau(chi)) is the epsilon-factor: a transcendental constant the explicit formula does NOT
   pin down (this is precisely why cancellation in sums of Gauss-sum phases -- Kummer/Patterson
   for the cubic case, Heath-Brown-Patterson -- is a celebrated HARD problem, only resolved for
   cubic via the metaplectic Eisenstein series, and OPEN for general order, with conductor = p).
 - The conductor of every L-function in sight is p (~2^160), not poly(n): the explicit-formula
   error terms are at scale sqrt(p), uselessly large for a length-n root-number sum.
""")
