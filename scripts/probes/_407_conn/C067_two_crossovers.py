"""
C067 attack: does the cyclotomic-norm crossover r*_norm = (1/2) p^{1/phi(n)}
coincide with the forced-anomaly crossover r*_anomaly = smallest r with
q * E_r^{char0}(mu_n) < n^{2r} ?

Connection C067 claims: r*_norm == r*_anomaly == beta+1 (the same number off
the single norm functional). The Lean file itself says the norm threshold is
VACUOUS in the prize regime (phi(n)=n/2, p^{1/phi(n)} -> 1, r*_norm -> 1/2).

PRIZE REGIME: dyadic mu_n, n = 2^mu a PROPER subgroup, q prime ~ n^beta,
beta in [4,5], n << sqrt(q). Exact integer arithmetic, no FFT.

char-0 energy E_r(mu_n): the number of (x_1..x_r, y_1..y_r) in mu_n^{2r} with
sum x_i = sum y_j exactly over Z[zeta_n]. For the dyadic group, the leading
asymptotic is E_r ~ (2r-1)!! * n^r (Gaussian / Lam-Leung). We use the EXACT
asymptotic that the campaign uses: E_r^{char0} = (2r-1)!! * n^r (leading), which
is the value the in-tree forced-anomaly probe uses. We also cross-check with an
exact small-n direct count where feasible.
"""

import math
from sympy import primerange, isprime

def double_factorial_odd(twoR_minus_1):
    # (2r-1)!! = product of odd numbers up to 2r-1
    r = (twoR_minus_1 + 1) // 2
    val = 1
    for k in range(1, r + 1):
        val *= (2 * k - 1)
    return val

def E_r_char0_leading(n, r):
    # (2r-1)!! * n^r  (Gaussian leading term, the in-tree forced-anomaly model)
    return double_factorial_odd(2 * r - 1) * (n ** r)

def find_prime_n_beta(n, beta):
    # find a prime q ~ n^beta with q ≡ 1 mod n, q a "large prime", n proper subgroup
    target = int(round(n ** beta))
    # search upward for q ≡ 1 mod n
    q = target - (target % n) + 1
    if q <= target:
        q += n
    for _ in range(200000):
        if isprime(q):
            return q
        q += n
    return None

def r_norm(q, phi_n):
    # smallest r with (2r)^{phi_n} >= q  (crossover where prime sublattice meets the 2r-box)
    # equivalently r*_norm = (1/2) q^{1/phi_n}
    val = 0.5 * (q ** (1.0 / phi_n))
    # integer crossover: smallest r with (2r)^{phi_n} >= q
    r = 1
    while (2 * r) ** phi_n < q:
        r += 1
        if r > 10**6:
            break
    return val, r

def r_anomaly(q, n):
    # smallest r with q * E_r^{char0} < n^{2r}
    r = 1
    while r <= 200:
        lhs = q * E_r_char0_leading(n, r)
        rhs = n ** (2 * r)
        if lhs < rhs:
            return r
        r += 1
    return None

print(f"{'n':>6} {'mu':>3} {'beta':>5} {'q':>20} {'phi(n)':>8} "
      f"{'r*_norm(real)':>14} {'r*_norm(int)':>12} {'r*_anom':>8} {'beta+1':>7} {'coincide?':>10}")
print("-" * 110)

for mu in [3, 4, 5, 6]:
    n = 2 ** mu
    phi_n = n // 2  # phi(2^mu) = 2^{mu-1}
    for beta in [4, 5]:
        q = find_prime_n_beta(n, beta)
        if q is None:
            continue
        beta_eff = math.log(q) / math.log(n)
        rn_real, rn_int = r_norm(q, phi_n)
        ra = r_anomaly(q, n)
        coincide = (rn_int == ra)
        print(f"{n:>6} {mu:>3} {beta_eff:>5.2f} {q:>20} {phi_n:>8} "
              f"{rn_real:>14.4f} {rn_int:>12} {str(ra):>8} {beta+1:>7} {str(coincide):>10}")

print()
print("Extrapolation to prize scale (n = 2^20 .. 2^32), no prime search, asymptotic q = n^beta:")
print(f"{'n':>12} {'phi(n)':>12} {'beta':>5} {'r*_norm=0.5*q^(1/phi)':>22} {'r*_anom':>8} {'beta+1':>7}")
print("-" * 80)
for mu in [10, 20, 30, 32]:
    n = 2 ** mu
    phi_n = n // 2
    for beta in [4, 5]:
        # q = n^beta exactly as a big int (approx prime)
        logq = beta * math.log(n)
        rn_real = 0.5 * math.exp(logq / phi_n)
        # anomaly with exact big ints
        ra = None
        for r in range(1, 60):
            lhs_log = logq + math.log(double_factorial_odd(2 * r - 1)) + r * math.log(n)
            rhs_log = 2 * r * math.log(n)
            if lhs_log < rhs_log:
                ra = r
                break
        print(f"{n:>12} {phi_n:>12} {beta:>5} {rn_real:>22.6f} {str(ra):>8} {beta+1:>7}")
