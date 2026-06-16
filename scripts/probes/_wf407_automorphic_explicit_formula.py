"""
#407 NOVEL ANGLE: automorphic explicit-formula for the Jacobi-sum Hecke L-function.

Goal: does the EXPLICIT FORMULA for the Hecke L-function attached to the Jacobi-sum
Grossencharacter, with the best UNCONDITIONAL zero-density / subconvexity, give
M := max_{b!=0}|eta_b| <= C sqrt(n log m) at the prize?

We need to determine, RIGOROUSLY, three quantities and then check the explicit-formula
error is non-vacuous at the prize:

  (A) WHICH Hecke L-function governs the family {eta_b} (equivalently {J(chi^i,chi^h)})?
  (B) Its CONDUCTOR (the analytic conductor entering the explicit-formula error).
  (C) The number of statistics we average over, and the target cancellation level.

KEY STRUCTURAL FACTS (Weil 1952 "Jacobi sums as Grossencharacters"):
  - For the field K = Q(zeta_n) (n = 2^a here), the Jacobi sums J(chi^i, chi^j), as the
    prime p (= a prime of K above the rational prime, split since p = 1 mod n) varies,
    are the values of a Hecke Grossencharacter ("Jacobi sum Hecke character") of K of a
    specific infinity-type, with conductor dividing n^2 (a power of the prime 2 here,
    since n = 2^a; the conductor is supported on primes dividing n and on infinity).
  - The associated Hecke L-function L(s, psi_Jac) is the L-function of a CM motive
    (a piece of the Jacobian of the Fermat curve x^n + y^n = 1). Its analytic conductor
    at the relevant point is q_an = D_K * N(f) * (archimedean part), where
       D_K = |disc Q(zeta_n)|,  N(f) = norm of the conductor ideal.

CRUCIAL DISTINCTION from the geometric (Deligne-Katz) side already in tree:
  - The geometric side bounds ONE Frobenius trace (Jacobi sum) at ONE prime p:
    |J| = sqrt(p), no cancellation in the average -> the EffKatz conductor = Theta(n),
    pointwise bound n/sqrt(p) vacuous.
  - The AUTOMORPHIC side instead studies the L-function as the prime p VARIES over
    a fixed K = Q(zeta_n), and uses the explicit formula to get equidistribution of
    the Frobenius angles {arg J(chi^i,chi^h)} -- BUT the prize FIXES p and varies the
    EXPONENTS (i,j) (i.e. the residue characters chi^i), not the prime.

THIS IS THE FATAL MISMATCH we test below. The Weil Grossencharacter packages the
variation IN p (the prime of K), giving a single L-function per (n, infinity-type).
The prize sum eta_b / T_h averages over the m EXPONENTS i at a SINGLE fixed prime p.
That is a sum over the DUAL group (residue characters), NOT over primes of K.
"""
import math
def log2(x): return math.log(x, 2.0)

print("="*78)
print("(A)-(C): The two distinct parametrizations -- where the Weil Hecke character lives")
print("="*78)
print("""
Weil's Jacobi-sum Grossencharacter J_{a,b} of K=Q(zeta_n):
   it is a function on the IDEALS/IDELES of K. Its value at a degree-1 prime P of K
   above a rational prime ell (ell = 1 mod n) is the Jacobi sum J_{a,b}(chi_P), where
   chi_P is the n-th power residue character mod P.  As P (equiv. ell) varies, these
   Jacobi sums lie on the circle of radius sqrt(N P) = sqrt(ell): the L-function
   L(s,J_{a,b}) = prod_P (1 - J_{a,b}(P) N(P)^{-s})^{-1}  is a degree-1 Hecke L-function
   (GL(1)/K), entire, with a functional equation s <-> 1-s (after normalizing weight).

   --> The 'prime' variable of THIS L-function is the prime P of K (i.e. the rational
       prime ell that splits in K).  THE EXPONENTS (a,b) are FIXED; they index WHICH
       Grossencharacter.
""")

print("PRIZE family by contrast:")
print("""
   eta_b = sum_{x in mu_n} psi(bx),  one FIXED prime p,  b ranges over Z/m.
   T_h   = (1/m) sum_{i=0}^{m-1} J(chi^i, chi^h),  one FIXED prime p, i ranges over Z/m.
   The average is over i = the EXPONENT (which power of the fixed order-m character chi),
   i.e. over the m residue characters of F_p of order dividing m, at the SINGLE prime p.
""")

print("="*78)
print("THE MISMATCH, quantified")
print("="*78)
print("""
   In Weil's package, fixing (a,b) and varying the prime ell of Q(zeta_n) gives ONE
   L-function whose Euler factors are indexed by primes ell -> infinity. The explicit
   formula controls  sum_{ell <= X} (coeff)  as X -> infinity:  a LONG sum over primes.

   The prize T_h is a FINITE sum of m Jacobi sums  J(chi^i, chi^h),  i = 0..m-1,
   ALL at the same prime p, with VARYING exponent i. As i varies, chi^i ranges over the
   m characters of order | m. The map  i |-> J(chi^i, chi^h)  is NOT the coefficient
   sequence of a single Hecke L-function over a FIXED number field: it is the restriction
   of the Jacobi-sum function to the FIBER over a single prime p, sampled along the
   character-exponent direction.
""")

# Now: is there an L-function whose Dirichlet coefficients ARE i -> J(chi^i, chi^h)?
# That would be an L-function "in the i (exponent / dual) variable", i.e. over Z/m or
# over the field Q(zeta_m). Let's see what its conductor and length would have to be.
print("="*78)
print("Can we instead build an L-function in the EXPONENT direction (over Q(zeta_m))?")
print("="*78)
print("""
   To apply an explicit formula to  T_h = (1/m) sum_i J(chi^i, chi^h),  we would want an
   L-function L(s) = sum_i lambda_i i^{-s} (or over ideals of Q(zeta_m)) with
   lambda_i = J(chi^i, chi^h)/sqrt(p). Two obstructions:

   (O1) FINITE LENGTH = NO ANALYTIC CONTINUATION GAIN. The sum has exactly m terms
        (i = 0..m-1), it is a COMPLETE character-exponent sum, not a tail of an Euler
        product. The explicit formula's power comes from trading a long prime sum for a
        short zero sum; here both sides are length ~ m. There is no asymptotic regime.

   (O2) THE EXPONENT MAP IS NOT MULTIPLICATIVE. J(chi^i, chi^h) as a function of i is
        NOT multiplicative in i (J(chi^{i1+i2},.) != J(chi^{i1},.) J(chi^{i2},.)): the
        Hasse-Davenport / Jacobi relations are J(chi^i,chi^h)=tau_i tau_h / tau_{i+h},
        an ADDITIVE-in-exponent cocycle, NOT an Euler product. So there is NO Euler
        factorization in i, hence no L-function, hence NO explicit formula in i.
""")

print("="*78)
print("CONDUCTOR of Weil's actual Hecke L-function (the one that DOES exist), and what")
print("its explicit formula gives -- to check if it is even relevant to the prize.")
print("="*78)

# K = Q(zeta_n), n = 2^a. disc(Q(zeta_{2^a})) = 2^{(a-1)2^{a-1}-1}... exact formula:
# disc(Q(zeta_{2^k})) = +/- 2^{(k-1)2^{k-1} - 1}  for k>=2  (degree phi(2^k)=2^{k-1}).
# Actually disc Q(zeta_{2^k}) = (-1)^{2^{k-2}} 2^{(k-1)2^{k-1}-1}. Magnitude:
def log2_disc_Qzeta_2k(k):
    # degree d = 2^{k-1}; |disc| = 2^{(k-1)2^{k-1} - 1} for k>=2
    if k < 2: return 0.0
    return (k-1)*2.0**(k-1) - 1.0

# conductor ideal f of the Jacobi-sum Grossencharacter: supported at primes | n and infinity.
# For the Fermat-Jacobi character of Q(zeta_n), the finite conductor divides (n)^2 = (2^a)^2;
# norm N((2^a)^2) over K... but the ANALYTIC conductor of a GL1/K Hecke L-fn is
#   q_an ~ |disc K| * N(f) * prod_v (archimedean).
# We only need its log2 size vs n.
print(f"{'a':>3} {'deg K=phi(n)':>13} {'log2|disc K|':>13} {'log2 N(f)<=2a*deg':>18} {'log2 q_an':>11}")
for a in [10, 20, 30, 32, 40]:
    n = 2**a
    degK = 2**(a-1)            # phi(2^a) = 2^{a-1}
    log2discK = log2_disc_Qzeta_2k(a)
    # N(f): f | (n)^2 = (2)^{2a}; N((2)) over K = 2^{f_res * g}... but (2) is totally ramified
    # in Q(zeta_{2^a}): (2) = (1-zeta)^{phi}, so N((2)) = 2^{degK}. Thus N((2)^{2a}) = 2^{2a*degK}.
    log2Nf = 2.0*a*degK       # upper bound on log2 N(f)
    log2q_an = log2discK + log2Nf
    print(f"{a:>3} {degK:>13} {log2discK:>13.1f} {log2Nf:>18.1f} {log2q_an:>11.1f}")

print("""
READING: the analytic conductor q_an of Weil's Jacobi-sum Hecke L-function over
K = Q(zeta_{2^a}) is DOUBLE-EXPONENTIAL in a, i.e. EXPONENTIAL in n:
   log2 q_an ~ (a-1) 2^{a-1} + 2a*2^{a-1}  ~  (3a) * 2^{a-1}  =  Theta(n log n).
At a=32 (n=2^32): log2 q_an ~ 3*32*2^31 ~ 2^37.9 ... i.e. q_an ~ 2^{2^37}.
This conductor is NOT polynomial in n -- it is exp(Theta(n log n)). The conductor is
of the FIELD Q(zeta_n), whose degree phi(n)=n/2 alone makes everything exp(n).
""")
