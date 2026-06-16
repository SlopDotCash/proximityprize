"""
C060 attack: "Paley-Zygmund forbids spectral concentration: F2 holds only by
sign-cancellation; magnitudes are PINNED by proven moments (F5 E2=3n^2-3n, F7
Parseval var=n), the ONLY open freedom is the PHASE of the worst eta_b."

The central testable claim is the DECOUPLING:
    magnitude profile {||eta_b||^2}  ==  PROVEN (pinned by 1st+2nd moments)
    worst-case B = max_b ||eta_b||    ==  controlled only by PHASE (open, F16)

If true, then:
  (A) the two moments (M1 = sum ||eta_b||^2 = q*n ; M2 = sum ||eta_b||^4 = q*(3n^2-3n))
      should DETERMINE the magnitude profile tightly enough that B is essentially fixed,
      and the freedom that remains is genuinely the PHASE (argument) of eta_b, not |eta_b|.

  (B) B = max |eta_b| is a function of the MAGNITUDE profile alone (it is literally
      max of the magnitudes). So if the connection claims B is "phase-only / open",
      it must be claiming the magnitude profile itself is the open object -- contradicting
      "magnitudes are pinned".

We test (A) by: fixing the two proven moments M1, M2 at their EXACT in-regime values,
and asking how much freedom the max of a nonneg profile {x_b = ||eta_b||^2 } over q
frequencies has, subject ONLY to sum x_b = M1 and sum x_b^2 = M2. This is the moment
method's actual reach. If max(x) ranges over a WIDE interval -> magnitudes are NOT
pinned; the decoupling is false; B's freedom is a MAGNITUDE freedom the moments do not see.

We also compute the TRUE spectrum on real proper dyadic subgroups mu_n < F_q* to anchor.

Exact integer arithmetic for moments; high precision for the true spectrum maxima.
"""
import cmath, math
from math import gcd

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, beta_min, beta_max):
    """smallest prime q = 1 mod n with n^beta_min <= q <= n^beta_max, n a proper subgroup."""
    lo = max(n+1, int(n**beta_min))
    hi = int(n**beta_max)
    # q = 1 + k*n
    k = (lo - 1)//n
    if k < 1: k = 1
    while True:
        q = 1 + k*n
        if q > hi: return None
        if q > n and isprime(q):
            return q
        k += 1

def subgroup(g_gen, n, q):
    """the dyadic subgroup mu_n: need an element of order n. q-1 divisible by n."""
    # find a generator of F_q^*, then raise to (q-1)/n
    # simple: find primitive root
    def order(a):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
        return o
    # find primitive root
    g = None
    for cand in range(2, q):
        if order(cand) == q-1:
            g = cand; break
    h = pow(g, (q-1)//n, q)  # element of order n
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = (x*h) % q
    assert len(S) == n
    return sorted(S)

def true_spectrum(n, q):
    """eta_b = sum_{y in mu_n} exp(2 pi i b y / q), for all b. return list of |eta_b|."""
    S = subgroup(None, n, q)
    w = 2*math.pi/q
    mags = []
    for b in range(q):
        s = 0j
        for y in S:
            s += cmath.exp(1j*w*((b*y) % q))
        mags.append(abs(s))
    return mags

def max_given_moments(M1, M2, q, n):
    """
    Over nonneg profiles {x_b}, b=0..q-1, with sum x_b = M1 and sum x_b^2 = M2,
    what is the RANGE of max_b x_b? (x_b = ||eta_b||^2 >= 0.)

    The true profile additionally has x_0 = n^2 (eta_0 = n). We include that constraint
    in a 'with-trivial' variant.

    Upper bound on max under (sum, sum^2): put mass M on one coord, spread the rest
    (M1-M) as flatly as possible over the other q-1 coords. Then
       sum^2 = M^2 + (M1-M)^2/(q-1)  must equal M2.
    Solve for the largest feasible M. That is the moment method's *upper* reach for max.
    Lower bound on max: max >= M1/q (flat) and max >= sqrt(M2/q).
    """
    # largest M with M^2 + (M1-M)^2/(q-1) <= M2  (>= because spreading the rest only
    # at minimum sum^2 = (M1-M)^2/(q-1); any other spreading gives larger sum^2, so to
    # ALLOW a given M we need its minimal companion sum^2 <= M2).
    qm1 = q-1
    # maximize M subject to f(M)=M^2 + (M1-M)^2/qm1 <= M2
    # f convex; feasible region is an interval [Mlo,Mhi]; we want Mhi.
    a = 1 + 1.0/qm1
    bb = -2*M1/qm1
    c = M1*M1/qm1 - M2
    disc = bb*bb - 4*a*c
    if disc < 0:
        return None
    Mhi = (-bb + math.sqrt(disc))/(2*a)
    Mlo = (-bb - math.sqrt(disc))/(2*a)
    max_lo = max(M1/q, math.sqrt(M2/q))
    return Mlo, Mhi, max_lo

print(f"{'n':>4} {'q':>8} {'beta':>5} | {'trueB':>9} {'B/sqrtn':>8} | "
      f"{'maxprof_lo(|eta|)':>16} {'maxprof_hi(|eta|)':>16} | {'sqrt_n':>7} {'sqrt(qn)':>9}")
print("-"*120)

cases = [(8,3.0,3.6),(16,3.0,3.6),(32,2.5,3.2),(64,2.5,3.0)]
for n, bmin, bmax in cases:
    q = find_prime(n, bmin, bmax)
    if q is None:
        print(f"{n} no prime"); continue
    beta = math.log(q)/math.log(n)
    mags = true_spectrum(n, q)
    # B = max over b != 0
    Bsq = max(m*m for b,m in enumerate(mags) if b != 0)
    B = math.sqrt(Bsq)
    # exact moments (closed form, in-regime SidonModNeg holds for these proper dyadic subgroups
    # when q large; but we use the ACTUAL computed moments to be safe)
    M1 = sum(m*m for m in mags)            # = q*n exactly
    M2 = sum(m**4 for m in mags)           # = q*E2(G)
    res = max_given_moments(M1, M2, q, n)
    if res is None:
        print(f"{n} {q} infeasible"); continue
    Mlo, Mhi, max_lo = res
    # convert x = ||eta||^2 ranges back to |eta| scale
    print(f"{n:>4} {q:>8} {beta:>5.2f} | {B:>9.3f} {B/math.sqrt(n):>8.3f} | "
          f"{math.sqrt(max(Mlo,0)):>16.3f} {math.sqrt(Mhi):>16.3f} | "
          f"{math.sqrt(n):>7.3f} {math.sqrt(q*n):>9.2f}")

print()
print("INTERPRETATION:")
print(" - The columns maxprof_lo/hi give the RANGE of max_b|eta_b| compatible with the")
print("   EXACT proven moments M1=q*n, M2=q*(3n^2-3n). This is what the moments 'pin'.")
print(" - If [lo,hi] is a WIDE interval that brackets trueB very loosely, then the moments")
print("   DO NOT pin the magnitude profile / B: the worst-case magnitude itself is free,")
print("   so the open object is a MAGNITUDE freedom, not a 'phase-only' freedom.")
