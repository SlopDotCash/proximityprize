"""
C047 attack: "No union/Chernoff bridges average->worst on the line family; the
floor is a measure-zero outlier (witness spread exponentially rare)."

The connection (rank 47) asserts a META claim about TECHNIQUE:
  (1) line_first_moment_bound (in-tree, PROVEN): per-line first moment
        M = sum_gamma |Lambda(gamma,a)| obeys  M * a <= |C| * n,
      i.e. average per-line list mass is field-size-independent ~ poly(n)/a.
  (2) The explicit witness-spread constructions cap the number of DISTINCT
      bad scalars at  n-1  (constCode) and  (k+1)(n-k-1)+1 = Theta(n^2)
      (sharp arithmetic spread).
  (3) The "floor" (a delta* lower bound that beats the trivial) needs
        I(delta) ~ q * eps*    bad scalars in the window.
  (4) The MDS first moment  E_line[I] = q^{k+1} * V_{delta n} / q^n  (expected
      incidence of a random line against the weight-floor(delta n) ball) is
      ASTRONOMICALLY below n.
  Conclusion: worst far-line incidence is a measure-zero outlier vs an
  exponentially smaller average -> no Chernoff/union/Chebyshev bound bridges
  average -> worst; the tail to order log n IS the deep-moment (BGK) input.

We attack by EXACT computation in the PRIZE REGIME (proper dyadic subgroup
mu_n < F_q*, q prime = 1 mod n, n << sqrt q), checking each numerical clause:
  A. avg-vs-floor:   E_line[I]  vs  floor target q*eps*  (does avg << floor?)
  B. max/avg ratio:  does the worst-case incidence / average DIVERGE?  (extreme
                     value, so concentration cannot certify the floor)
  C. explicit spread Theta(n^2) vs floor target q*eps* (is the in-tree
     single-line ceiling below the budget? = the realized eps_mca is sub-prize)
  D. the Chernoff/union no-go: is the *variance/tail* of line incidence
     dominated by its mean (so Chebyshev gives nothing past the mean)?

All exact-integer (Python big ints). We do NOT need q huge for the structural
ratios; we report the law and extrapolate the closed forms to the true prize
n=2^30, eps*=2^-128.
"""

from math import comb, log2, sqrt

# ---- prize-regime proper-subgroup primes (n = 2^mu | q-1, q prime, n << sqrt q) ----
# (n, q): dyadic subgroup mu_n is a PROPER subgroup of F_q^*.
CASES = [
    (8,    1009),   # beta = log_n q = 3.32
    (16,   7681),   # 3.23
    (32,   12289),  # 2.72  (the canonical FRI-ish prime)
    (64,   65537),  # 2.67
    (8,    65537),  # n small, q large: beta = 5.33  (a high-beta prize-like row)
    (16,   65537),  # beta = 4.0
    (32,   1073750017),  # 32 | q-1, q ~ 2^30, beta ~ 6.0  (deep prize-like)
]

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def ball_volume(n, q, w):
    """|Hamming ball of radius w in F_q^n| over the weight (number of words of
    weight <= w) -- but for line-vs-ball INCIDENCE we want the SYNDROME ball in
    F_q^{n-k}: number of weight-<= w words. Use the standard volume."""
    return sum(comb(n, t) * (q-1)**t for t in range(w+1))

print("="*100)
print("C047: average (MDS first moment) vs worst-case line incidence, prize regime")
print("="*100)

# ---------- CLAUSE A & C: the law for the in-tree quantities ----------
# Rate rho = k/n. Use the prize rates {1/2,1/4,1/8} and the radius delta in the
# Johnson->capacity window. The explicit spread is (k+1)(n-k-1)+1.
print("\n[A/C] explicit single-line spread Theta(n^2) vs floor target q*eps*")
print(f"{'n':>4} {'q':>12} {'beta':>5} {'k':>4} {'explicitSpread':>16} "
      f"{'eps_realized':>14} {'q*eps* (floor)':>16} {'spread<floor?':>13}")
EPS_STAR = 2.0**-128
for (n, q) in CASES:
    assert is_prime(q) and (q-1) % n == 0, (n, q)
    beta = log2(q)/log2(n)
    for rho in (0.5, 0.25, 0.125):
        k = max(1, int(round(rho*n)))
        if k+1 > n: continue
        spread = (k+1)*(n-k-1) + 1            # sharp arithmetic ceiling (Theta(n^2))
        eps_realized = spread / q             # eps_mca lower bound realized in tree
        # floor target: a delta* certificate needs eps_mca >= eps*, i.e. needs
        # the bad-scalar count >= q*eps*.
        floor_count = q * EPS_STAR
        below = spread < floor_count
        print(f"{n:>4} {q:>12} {beta:>5.2f} {k:>4} {spread:>16} "
              f"{eps_realized:>14.3e} {floor_count:>16.3e} {str(below):>13}")

# ---------- CLAUSE A: MDS first moment E_line[I] ----------
# A random line {f + gamma g} in F_q^n, far-direction. The number of line points
# gamma at which the codeword (a fixed MDS/RS codeword, k<n) agrees with the line
# in >= a coords is the "incidence". The MDS first-moment heuristic the connection
# cites: E[I] = q^{k+1} * V_{delta n} / q^n  where V_{delta n} counts the words at
# distance <= delta n.  We compute it exactly and compare to the floor target.
print("\n[A] MDS first moment  E_line[I] = q^{k+1} V_{delta n} / q^n  vs floor q*eps*")
print(f"{'n':>4} {'q':>12} {'k':>4} {'delta':>6} {'a=ceil((1-d)n)':>15} "
      f"{'E_line[I]':>14} {'floor q*eps*':>14} {'avg<<floor?':>12}")
for (n, q) in CASES:
    for rho in (0.25,):
        k = max(1, int(round(rho*n)))
        # radius in the open window (1 - sqrt rho, 1 - rho - c/log n): take a
        # representative interior delta.
        johnson = 1 - sqrt(rho)
        cap = 1 - rho
        delta = (johnson + cap)/2
        w = int(delta*n)                      # weight floor
        a = n - w                             # agreement threshold a = n - w
        # exact (big-int) first moment:  q^{k+1} * V_w / q^n
        Vw = ball_volume(n, q, w)
        # E = q^{k+1} V_w / q^n   (rational; report log10 magnitude)
        # log10 E = (k+1-n) log10 q + log10 V_w
        import math
        logE = (k+1-n)*math.log10(q) + math.log10(Vw)
        floor_count = q*EPS_STAR
        logFloor = math.log10(floor_count)
        below = logE < logFloor
        print(f"{n:>4} {q:>12} {k:>4} {delta:>6.3f} {a:>15} "
              f"{('1e%+.1f'%logE):>14} {('1e%+.1f'%logFloor):>14} {str(below):>12}")

# ---------- CLAUSE B & D: max/avg ratio & Chernoff no-go, EXACT small n ----------
# Here we directly enumerate the *monomial line family* on the constant code and
# measure the empirical distribution of per-line incidence (number of bad scalars
# gamma whose window is a witness set), and compare worst-case to average and to
# a Chernoff/Chebyshev prediction. We use the in-tree construction: constant code
# C=RS[.,n,1], stack (i^2, i); bad scalars gamma_j = -(2j+1), each a DISTINCT
# witness window {j,j+1}. The far-line incidence I(gamma) = # windows on which
# the line f+gamma g is constant.
print("\n[B/D] per-scalar incidence distribution on the in-tree const-code line, exact")
print(f"{'n':>4} {'q':>12} {'#bad gamma (=spread)':>20} {'avg over F':>12} "
      f"{'max':>5} {'max/avg':>9} {'Var':>10} {'Cheby k-sig to reach max':>26}")
for (n, q) in CASES:
    if q > 200000:        # full F_q enumeration only feasible for small q
        print(f"{n:>4} {q:>12} {'(skip: q too large for full enum)':>20}")
        continue
    # over all gamma in F_q, count agreements of the line i^2 + gamma i with a
    # constant on consecutive windows -> the bad set is exactly the n-1 distinct
    # gamma_j = -(2j+1). incidence per scalar = # windows it kills.
    # For a *generic* gamma, line i^2+gamma i is constant on {j,j+1} iff
    # j^2+gamma j = (j+1)^2+gamma(j+1) <=> gamma = -(2j+1). So each gamma_j kills
    # exactly ONE window (the windows are disjoint in gamma); incidence is 0 or 1.
    # The interesting "line incidence vs a ball" quantity is the FULL
    # agreement-list count.  We instead measure: for each gamma, the max number
    # of coordinates on which i^2+gamma*i hits ANY single constant value (= the
    # heavy-decode count a single codeword achieves on that line). This is the
    # object line_first_moment_bound bounds.
    # value v(i) = i^2 + gamma i mod q; incidence = max multiplicity of a value.
    cnt = []
    for g in range(q):
        from collections import Counter
        c = Counter(((i*i + g*i) % q) for i in range(n))
        cnt.append(max(c.values()))
    avg = sum(cnt)/q
    mx = max(cnt)
    var = sum((x-avg)**2 for x in cnt)/q
    spread = n-1
    # to reach the max via Chebyshev from the mean you need (max-avg)/sqrt(var) sigmas
    ksig = (mx-avg)/sqrt(var) if var > 0 else float('inf')
    print(f"{n:>4} {q:>12} {spread:>20} {avg:>12.4f} {mx:>5} {mx/avg:>9.2f} "
          f"{var:>10.4f} {ksig:>26.2f}")

# ---------- EXTRAPOLATION to true prize ----------
print("\n[EXTRAP] true prize: n=2^30, eps*=2^-128, q ~ n*2^128 and q ~ n^4..n^5")
n = 2**30
for desc, q in [("q ~ n*2^128", n*(2**128)), ("q ~ n^4", n**4), ("q ~ n^5", n**5)]:
    spread = (n//4 + 1)*(n - n//4 - 1) + 1     # Theta(n^2) ceiling
    eps_realized = spread / q
    floor_count = q * EPS_STAR
    print(f"  {desc:>14}: log2 q={log2(q):7.1f}  spread~n^2=2^{log2(spread):4.1f}  "
          f"eps_realized=2^{log2(eps_realized):7.1f}  floor q*eps*=2^{log2(floor_count):6.1f}  "
          f"spread {'<' if spread<floor_count else '>='} floor")
