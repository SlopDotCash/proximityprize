"""
C080 attack: "The proven coset count m=(q-1)/n forces log m not log q; EVT floor sqrt(2 n log m) is
the correct target and Ramanujan 2 sqrt(n) is FALSE in regime."

The three IN-TREE proven facts (not in dispute, axiom-clean):
  (1) eta takes <= m=(q-1)/n distinct nonzero-freq values (Gauss periods)  [eta_image_card_mul_le]
  (2) (1/(q-1)) sum_{b!=0} ||eta_b||^2 = n     (per-period variance n)      [subgroup_gaussSum_secondMoment]
  (3) Ramanujan => PaleyFloor only when L=log m >= 4/C^2                    [ramanujan_implies_paleyFloor]

The LOAD-BEARING NOVEL claim of C080 (the EVT inferential leap):
   B := max_{b!=0} ||eta_b||  ~  sqrt(2 n ln m)   (max of m mean-zero variance-n quasi-Gaussians)
and the attack-plan test:  B/sqrt(2 n ln m) -> 1   AND   B/(2 sqrt n) -> infinity.

We test BOTH directions at PROPER dyadic subgroups, LARGE primes, beta ~ 4-5, n << sqrt(q),
multiple primes per n (avoiding the #400 full-group trap).

EXACT arithmetic for the subgroup; double-precision complex exp for the O(sqrt q) magnitudes
(standard; magnitudes are ~sqrt q so well-conditioned). We compute the EXACT max over ALL b in F_p
(so B is the true worst period, not a sample).
"""
import numpy as np
from sympy import isprime, primitive_root
import math

def true_B_and_stats(p, n):
    g = int(primitive_root(p))
    m = (p - 1) // n
    gm = pow(g, m, p)
    sub = []
    cur = 1
    for _ in range(n):
        sub.append(cur)
        cur = (cur * gm) % p
    sub = np.array(sub, dtype=np.int64)
    w = np.exp(2j * np.pi * np.arange(p) / p)
    bs = np.arange(1, p)
    eta = np.zeros(p - 1, dtype=complex)
    for x in sub:
        eta += w[(bs * x) % p]
    a = np.abs(eta)
    B = a.max()
    meansq = (a ** 2).mean()      # should be ~ n  (per-period/per-freq variance)
    ndistinct = len(set(np.round(eta, 5)))
    return B, meansq, ndistinct, m

# dyadic n = 2^mu, PROPER subgroup, p = 1 mod n prime, p ~ n^beta with beta ~ 4-5, n << sqrt(q).
# We pick the SMALLEST prime >= n^beta with p = 1 mod n, for beta in {4, 4.5, 5} where feasible
# (exact max over all b limits p to ~few x 10^5 for runtime; n up to 32 keeps beta>=3.6).
def find_prime(n, target):
    p = target - (target % n) + 1
    if p <= n: p += n
    while True:
        if p > n and isprime(p):
            return p
        p += n

print("=== C080: EVT floor sqrt(2 n ln m) vs TRUE B = max_{b!=0}||eta_b|| (proper subgroups) ===")
print(f"{'n':>4} {'p':>9} {'beta':>5} {'m':>8} {'#dist':>7} {'meansq/n':>9} "
      f"{'B':>9} {'2sqrtn':>8} {'floor=sq(2nlnm)':>15} {'B/floor':>8} {'B/(2sqn)':>9}")
rows = []
configs = []
for mu in [3, 4, 5]:           # n = 8, 16, 32
    n = 2 ** mu
    for beta in [3.5, 4.0, 4.5]:
        target = int(round(n ** beta))
        if target > 600000:    # keep exact-over-all-b tractable
            continue
        p = find_prime(n, target)
        if p > 700000:
            continue
        configs.append((n, p, beta))

for (n, p, beta) in configs:
    B, meansq, nd, m = true_B_and_stats(p, n)
    beta_real = math.log(p) / math.log(n)
    twosqrtn = 2 * math.sqrt(n)
    floor = math.sqrt(2 * n * math.log(m))
    rows.append((n, p, beta_real, m, B, meansq, twosqrtn, floor))
    print(f"{n:>4} {p:>9} {beta_real:>5.2f} {m:>8} {nd:>7} {meansq/n:>9.3f} "
          f"{B:>9.3f} {twosqrtn:>8.3f} {floor:>15.3f} {B/floor:>8.3f} {B/twosqrtn:>9.3f}")

print()
print("INTERPRETATION KEYS:")
print(" - meansq/n ~ 1 confirms in-tree fact (2): per-period variance = n.")
print(" - B/(2 sqrt n): if this GROWS with m (at fixed n), Ramanujan cap 2sqrt(n) is FALSE in regime.")
print(" - B/floor where floor=sqrt(2 n ln m): C080 predicts -> 1. Test whether it CONVERGES to 1,")
print("   stays bounded O(1) (=> correct SCALE but wrong constant), or trends (=> wrong law).")

# Direction test: hold n FIXED, grow m (i.e. grow p / beta), watch B/(2sqrtn) and B/floor.
print()
print("=== Fixed-n, growing-m trend (n=16): does B/(2sqrtn) diverge and B/floor stabilize? ===")
n = 16
print(f"{'p':>9} {'m':>8} {'B':>9} {'B/(2sqn)':>9} {'B/floor':>8}")
for beta in [3.0, 3.5, 4.0, 4.25, 4.5]:
    target = int(round(n ** beta))
    if target > 600000:
        continue
    p = find_prime(n, target)
    if p > 700000:
        continue
    B, meansq, nd, m = true_B_and_stats(p, n)
    twosqrtn = 2 * math.sqrt(n)
    floor = math.sqrt(2 * n * math.log(m))
    print(f"{p:>9} {m:>8} {B:>9.3f} {B/twosqrtn:>9.3f} {B/floor:>8.3f}")
