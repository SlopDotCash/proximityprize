#!/usr/bin/env python3
"""
probe(#444): DIGIT-RECURSION STEPANOV assessment for M(n)=max_{b!=0}|sum_{x in mu_n} e_p(bx)|.

LEAD (untried, family ii): a multivariate dyadic-DIGIT-recursion Stepanov auxiliary where
multiplicity comes from the x->x^2 RECURSION on mu_n = {x : x^{2^mu}=1}, transverse to the
univariate tangency orbit that killed earlier Stepanov, exploiting the 2-power tower.

Assess: can it give a sub-sqrt(p) level-set bound at beta=4, or does it die at the HBK p^{1/3}
boundary like univariate Stepanov?

We test the ACTUAL mechanism a Stepanov bound for a character sum needs. The Stepanov/Mit'kin/
Heath-Brown-Konyagin route to "M(n) small" reduces to a LEVEL-SET / point-count bound: if |eta_b|
is large then many x in mu_n satisfy a structured relation, and a Stepanov auxiliary Psi vanishing
to multiplicity M at each such x bounds their number by deg(Psi)/M. The reach is:

    #{relevant points} * M  <=  deg(Psi).

The DIGIT-RECURSION HOPE: the map sigma: x -> x^2 permutes/maps mu_{2^mu} into itself (it's the
shift on the 2-adic digit tower). An auxiliary built to be sigma-covariant -- Psi(x^2) related to
Psi(x)^2 -- could vanish to high order via the RECURSION (each digit level adds multiplicity),
giving M ~ mu = log2(n) FOR FREE, transverse to univariate tangency. We test whether that actually
beats the degree.

ALL subgroups PROPER (n | p-1, n < p), p >> n^3, never the full group.
"""
import numpy as np
from itertools import product

# ----------------------------------------------------------------------------
# Number-theory helpers
# ----------------------------------------------------------------------------
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
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

def find_prime(n, beta_min=3.0, start_mult=2):
    """Find prime p = m*n+1 with p >= n^beta_min (PROPER subgroup, p >> n^3)."""
    target = n**beta_min
    k = max(start_mult, int(np.ceil(target/n)))
    while True:
        p = k*n+1
        if p > n and is_prime(p):
            return p
        k += 1

def subgroup_gen(p, n):
    """Return a generator of the order-n subgroup mu_n of F_p^*."""
    g = 2
    while pow(g, (p-1)//2, p) == 1 or pow(g, (p-1)//n, p) == 1 and n>1:
        g += 1
    # element of order n
    h = pow(g, (p-1)//n, p)
    # verify order exactly n
    assert pow(h, n, p) == 1
    for d in range(1, n):
        if n % d == 0 and pow(h, d, p) == 1 and d < n:
            # not primitive; retry with another base
            pass
    return h

def mu_n_set(p, n):
    h = subgroup_gen(p, n)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = x*h % p
    assert len(S) == n, (len(S), n)
    return sorted(S)

def M_of_n(p, n):
    """Exact M(n) = max_{b!=0} |sum_{x in mu_n} e_p(b x)|, b ranging over coset reps
    F_p^*/mu_n (eta is orbit-invariant). Returns (M, sqrt(n*log m) target)."""
    S = np.array(mu_n_set(p, n), dtype=np.int64)
    m = (p-1)//n
    # eta_b is invariant under b -> zeta*b for zeta in mu_n; distinct periods indexed by quotient.
    # Just range b over 1..p-1 but that's p evals; for exactness on small p do all b.
    best = 0.0
    # group b by coset: pick one rep per coset for efficiency
    seen = set()
    h = subgroup_gen(p, n)
    reps = []
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        x = b
        for _ in range(n):
            seen.add(x); x = x*h % p
    for b in reps:
        ang = 2*np.pi*(b*S % p)/p
        val = abs(np.sum(np.exp(1j*ang)))
        if val > best: best = val
    import math
    target = math.sqrt(n*math.log(m)) if m > 1 else float('nan')
    return best, target, m

# ----------------------------------------------------------------------------
# THE DIGIT-RECURSION STEPANOV TEST
# ----------------------------------------------------------------------------
# Core: mu_n = {x : x^n - 1 = 0}, n = 2^mu. The squaring map sigma(x)=x^2 sends mu_{2^mu} ->
# mu_{2^{mu-1}} (a 2-to-1 tower projection). A "digit-Stepanov" auxiliary would vanish on mu_n
# to multiplicity boosted by climbing the digit tower.
#
# THE DECISIVE QUESTION (what kills or saves it):
# Any auxiliary Psi that vanishes to order M at every point of a target set T subset F_p must have
#   deg Psi >= |T| * M.
# For a character-sum bound we need T = the relevant level set (size ~ n / something) and M as
# large as possible WITHOUT inflating deg Psi past sqrt(p).
#
# The univariate Stepanov ceiling: deg Psi ~ |T| * M, M is FREE only up to the order the field
# allows; the construction's deg is dominated by an X^p-type Frobenius substitution giving
# deg ~ p^{1/2} (Stepanov/Schmidt) or via HBK refinement deg ~ p^{1/3} for the BEST sub-multiplicative
# bound, with the level set being mu_n itself (|T| = n). Reach: n <= deg/M ~ p^{1/3}/1, i.e. the
# method only controls subgroups up to n ~ p^{1/3}. THAT is the p^{1/3} boundary.
#
# Does digit-recursion CHANGE |T|*M <= deg? We test whether a sigma-covariant auxiliary can have
# M (per-point multiplicity on mu_n) GROW with mu = log2 n while deg stays ~ sqrt(p) or below.
# If M can be ~ mu transverse-for-free, reach becomes n <= deg/mu ~ sqrt(p)/log n -- still NOT
# better than sqrt(p), and the level set T driving M(n) has |T| ~ n. So we test the identity wall:
#   does sigma-covariance FORCE |T|*M to track deg with NO digit discount?

def digit_recursion_multiplicity_test(mu_max=8):
    """
    Test the algebraic heart: build the lowest-degree polynomial Psi over Q (char 0, then we check
    char p) that is sigma-COVARIANT on mu_{2^mu} and vanishes on mu_n. Measure (deg Psi) vs the
    multiplicity M it achieves at each point and the level-set size |T| it can cover.

    Mechanism under test: the recursion Psi_{k+1}(x) = Psi_k(x) * Psi_k(-x) [or x->x^2 pullback]
    gives vanishing on the 2-tower. We measure if multiplicity per mu_n-point exceeds 1 WITHOUT
    degree blowup, i.e. whether the digit tower yields FREE multiplicity.
    """
    import sympy
    X = sympy.symbols('X')
    print("="*78)
    print("DIGIT-RECURSION COVARIANT AUXILIARY: does x->x^2 give FREE multiplicity on mu_n?")
    print("="*78)
    print(f"{'mu':>3} {'n':>5} {'construction':>34} {'deg':>6} {'mult@mu_n':>10} {'deg/(n*M)':>10}")
    for mu in range(1, mu_max+1):
        n = 2**mu
        # The natural sigma-covariant vanisher on mu_n is X^n - 1 itself (vanishes order 1 at each
        # of n points, deg n). Digit recursion: X^n-1 = prod_{k<mu}(X^{2^k}+1)*(X-1)*(X+1)... the
        # cyclotomic factorization. Squaring x->x^2 maps roots of X^{2^k}+1 to roots of X^{2^{k-1}}+1.
        # A covariant HIGH-MULTIPLICITY vanisher: (X^n - 1)^M has deg n*M, mult M -- the TRIVIAL one.
        # The QUESTION: is there a LOWER-degree poly with mult M at all n points? NO: any poly
        # vanishing to order M at n distinct points has deg >= n*M (it's divisible by (X^n-1)^M).
        # The digit recursion does NOT change this -- it's the same n distinct points.
        Psi_triv = (X**n - 1)
        deg_triv = n
        # Best covariant multiplicity-M construction at fixed target deg D=sqrt(p)-surrogate:
        # M_max = floor(D / n). The recursion gives NO discount on the n*M lower bound.
        # Demonstrate: the squaring pullback Psi(X^2) has roots = sqrt of mu_n roots = mu_{2n},
        # NOT higher multiplicity on mu_n. So x->x^2 SPREADS to a bigger set, doesn't concentrate.
        Psi_pull = sympy.expand((X**n - 1).subs(X, X**2))  # = X^{2n}-1, roots mu_{2n}, mult still 1
        deg_pull = 2*n
        # multiplicity of Psi_pull at a point of mu_n: a generic mu_n point is a root of X^{2n}-1
        # too (mu_n subset mu_{2n}), with multiplicity 1 (X^{2n}-1 squarefree). So pullback gives
        # mult 1, deg 2n -- STRICTLY WORSE ratio than triv.
        mult_at_mun = 1  # X^{2n}-1 is squarefree over Q and over F_p for p odd, p ∤ 2n
        ratio = deg_pull / (n * mult_at_mun)
        print(f"{mu:>3} {n:>5} {'Psi(X^2)=X^{2n}-1 (pullback)':>34} {deg_pull:>6} {mult_at_mun:>10} {ratio:>10.3f}")
    print()
    print("KEY: the squaring pullback X->X^2 maps mu_n INTO mu_{2n} (SPREADS the set, 2-to-1 cover),")
    print("it does NOT concentrate multiplicity on mu_n. Multiplicity at mu_n points stays 1 while")
    print("degree DOUBLES. The digit recursion gives NEGATIVE multiplicity discount, not free mult.")

# ----------------------------------------------------------------------------
# THE HARD WALL: |T|*M <= deg is an IDENTITY, independent of how M is obtained
# ----------------------------------------------------------------------------
def stepanov_reach_vs_pthird(verbose=True):
    """
    The Stepanov reach for controlling M(n) on mu_n: the level set driving |eta_b| has |T| ~ n
    (the whole subgroup), and any vanishing auxiliary obeys |T|*M <= deg. The BEST degree any
    Stepanov construction achieves for a subgroup of F_p (Stepanov ~ p^{1/2}, HBK ~ p^{1/3} for
    the multiplicative-energy refinement). Reach: n <= deg => n <= p^{1/3} (HBK boundary).

    We tabulate, for the prize family, where digit-recursion would have to land to beat sqrt(p),
    and confirm it lands ABOVE the p^{1/3} wall (so it dies there, like univariate Stepanov).
    """
    import math
    print("="*78)
    print("STEPANOV REACH vs HBK p^{1/3} BOUNDARY (prize family p ~ n^beta, beta=4)")
    print("="*78)
    print(f"{'mu':>3} {'n=2^mu':>10} {'p~n^4':>14} {'p^{1/3}':>12} {'p^{1/2}=target M':>16} {'n vs p^{1/3}':>14}")
    for mu in [10, 20, 30]:
        n = 2**mu
        beta = 4
        p = n**beta
        p13 = p**(1/3)
        p12 = p**(1/2)
        verdict = "n >> p^{1/3}  (DEAD)" if n > p13 else "n <= p^{1/3} (alive)"
        print(f"{mu:>3} {n:>10} {p:>14.3e} {p13:>12.3e} {p12:>16.3e} {verdict:>22}")
    print()
    print("At beta=4: n = p^{1/4} >> p^{1/3}? NO: p^{1/4} < p^{1/3}. Let's check carefully.")
    print("  n = p^{1/beta} = p^{1/4}.  HBK boundary is n <= p^{1/3}.  Since 1/4 < 1/3, n=p^{1/4} < p^{1/3}.")
    print("  So n IS below the p^{1/3} boundary at beta=4 -- HBK/Stepanov reach IS in regime!")
    print("  BUT: the bound HBK delivers there is M(n) <= n^{1-delta} (BGK-type, delta->0), NOT sqrt(n log m).")

if __name__ == "__main__":
    # Part 1: the covariance/free-multiplicity test (algebraic heart)
    digit_recursion_multiplicity_test(mu_max=8)
    print()
    # Part 2: the reach-vs-boundary arithmetic
    stepanov_reach_vs_pthird()
    print()
    # Part 3: EXACT M(n) ground truth on small PROPER subgroups (for calibration)
    print("="*78)
    print("EXACT M(n) ground truth (PROPER mu_n, p >> n^3) -- what Stepanov must beat")
    print("="*78)
    print(f"{'n':>5} {'p':>10} {'m':>8} {'M(n)':>10} {'sqrt(n log m)':>14} {'M/target':>10} {'p^{1/3}':>10} {'n<=p13?':>8}")
    for n in [4, 8, 16, 32]:
        p = find_prime(n, beta_min=4.0)
        M, target, m = M_of_n(p, n)
        p13 = p**(1/3)
        print(f"{n:>5} {p:>10} {m:>8} {M:>10.3f} {target:>14.3f} {M/target:>10.3f} {p13:>10.1f} {str(n<=p13):>8}")
