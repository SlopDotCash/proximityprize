"""
C035 probe: Two-sided reverse-Markov moment-ratio bracket for the worst Gauss period.

The two in-tree bricks (exact, axiom-clean):
  UPPER (GaussPeriodMomentBound.eta_pow_le_of_energyBound):
      max_b ||eta_b||^{2r} <= q * E_r           (single term <= full 2r-th moment = q E_r)
   => max_b ||eta_b||^2 <= (q E_r)^{1/r}
  LOWER (WorstPeriodMomentRatioLower.exists_period_sq_ge_moment_ratio):
      max_{b!=0} ||eta_b||^2 >= (q E_r - n^{2r}) / (q E_{r-1} - n^{2(r-1)})

Here E_r = rEnergy(G,r) = #{(v,w) in G^r x G^r : sum v = sum w}  (FIELD-ADDITIVE energy
of the multiplicative subgroup G = mu_n inside F_q, addition mod p). This is EXACTLY the
object the Lean `rEnergy` computes and the moment identity sum_b ||eta_b||^{2r} = q E_r uses.

C035 claim under test:
  (a) the LOWER bracket (q E_r - n^{2r})/(q E_{r-1} - n^{2(r-1)}) genuinely pins max^2 at
      ~ (2r-1) n (true-max-of-m sub-Gaussian) so the two sides meet at r ~ log m;
  (b) the prize reduces to the single law E_r/E_{r-1} <= C * n (* log correction) at r ~ log m;
  (c) "the ratio telescopes away the (2r-1)!! prefactor, a cleaner object".

We compute, with EXACT integer arithmetic, at genuine prize-shaped primes (proper dyadic
subgroup mu_n, q = 1 mod n, large prime, n << sqrt q):
  - true B^2 = max_{b!=0} ||eta_b||^2   (exact via integer Gauss periods over Z[zeta_p]? -> use
    cyclotomic exact: eta_b are algebraic; we compute |eta_b|^2 to high precision and round)
  - E_r for r = 1..R  (exact integer counts, brute force over G^r)
  - UPPER^{1/r} = (q E_r)^{1/r}
  - LOWER ratio = (q E_r - n^{2r})/(q E_{r-1} - n^{2(r-1)})
  - the consecutive energy ratio E_r/E_{r-1}
and check whether E_r/E_{r-1} stays ~ n (the claimed law) or departs, and whether LOWER
actually reaches the prize scale n log m.
"""
import math, cmath
from sympy import isprime, primitive_root

def find_prime(n, beta_target):
    """smallest prime q = 1 mod n with q ~ n^beta_target, n a proper subgroup (q-1 > n)."""
    target = int(round(n ** beta_target))
    # search upward from target for q = 1 mod n prime, with (q-1)/n large (multiple primes)
    q = target - (target % n) + 1
    if q <= n: q += n
    while True:
        if q > n + 1 and isprime(q):
            return q
        q += n

def subgroup(n, q):
    """the unique order-n subgroup of F_q^* (q = 1 mod n)."""
    g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)  # order n
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = (x * h) % q
    assert len(set(G)) == n, "subgroup size wrong"
    return sorted(G)

def gauss_periods_sq(G, q):
    """exact-ish |eta_b|^2 for all b in F_q, eta_b = sum_{y in G} exp(2pi i b y / q).
       returns max over b != 0 of |eta_b|^2 (rounded to nearest int -- it IS an algebraic
       integer's abs-square but generally not rational; we report float)."""
    # |eta_b|^2 = sum_{y,y' in G} cos(2pi b (y - y')/q)
    best = -1.0
    w = 2 * math.pi / q
    for b in range(1, q):
        s = 0.0
        for y in G:
            for yp in G:
                s += math.cos(w * (b * (y - yp) % q))
        if s > best:
            best = s
    return best

def rEnergy(G, r, q):
    """exact E_r = #{(v,w) in G^r x G^r : sum v = sum w in F_q}.
       Compute via convolution: count of r-fold sumset multiplicities, then sum of squares."""
    # distribution of r-fold sums
    from collections import defaultdict
    cur = defaultdict(int)
    cur[0] = 1
    for _ in range(r):
        nxt = defaultdict(int)
        for s, c in cur.items():
            for y in G:
                nxt[(s + y) % q] += c
        cur = nxt
    # E_r = sum_s cur[s]^2
    return sum(c * c for c in cur.values())

print(f"{'n':>4} {'q':>10} {'beta':>5} {'m=(q-1)/n':>10} {'B^2':>10} {'B^2/n':>7}")
rows = []
for n, beta in [(8, 4.0), (8, 5.0), (16, 4.0), (16, 4.5), (32, 4.0), (32, 4.5)]:
    q = find_prime(n, beta)
    G = subgroup(n, q)
    m = (q - 1) // n
    realbeta = math.log(q) / math.log(n)
    # B^2 exact-numeric only feasible for modest q
    B2 = gauss_periods_sq(G, q) if q <= 60000 else None
    rows.append((n, q, realbeta, m, B2, G))
    b2s = f"{B2:10.2f}" if B2 is not None else "   (skip)"
    b2n = f"{B2/n:7.3f}" if B2 is not None else "   ---"
    print(f"{n:>4} {q:>10} {realbeta:5.2f} {m:>10} {b2s} {b2n}")

print()
print("=== Energy ratios E_r/E_{r-1} and the two brackets (exact integer E_r) ===")
print("Claim (c): E_r/E_{r-1} ~ n; LOWER ratio should pin B^2; UPPER^{1/r}=(qE_r)^{1/r}.")
print()
for (n, q, realbeta, m, B2, G) in rows:
    Rmax = 5 if n <= 16 else 4
    E = {0: 1}  # E_0 = 1 (empty sum: one solution 0=0)
    for r in range(1, Rmax + 1):
        E[r] = rEnergy(G, r, q)
    print(f"--- n={n} q={q} (beta={realbeta:.2f}) m={m} B^2={B2}  log m={math.log(m):.2f} ---")
    print(f"   {'r':>2} {'E_r':>16} {'E_r/E_(r-1)':>12} {'ratio/n':>8} "
          f"{'LOWER':>10} {'UPPER^1/r':>11} {'(2r-1)':>7}")
    for r in range(1, Rmax + 1):
        ratio = E[r] / E[r - 1]
        # LOWER bracket
        num = q * E[r] - n ** (2 * r)
        den = q * E[r - 1] - n ** (2 * (r - 1))
        lower = num / den if den > 0 else float('nan')
        upper = (q * E[r]) ** (1.0 / r)
        print(f"   {r:>2} {E[r]:>16} {ratio:12.3f} {ratio/n:8.3f} "
              f"{lower:10.2f} {upper:11.2f} {2*r-1:>7}")
    # where does LOWER peak (best lower bound on B^2)? and does it reach n*log m?
    lowers = []
    for r in range(1, Rmax + 1):
        num = q * E[r] - n ** (2 * r)
        den = q * E[r - 1] - n ** (2 * (r - 1))
        if den > 0:
            lowers.append((r, num / den))
    if lowers:
        rbest, lbest = max(lowers, key=lambda t: t[1])
        target = n * math.log(m)
        print(f"   best LOWER bound on B^2 = {lbest:.2f} at r={rbest};  "
              f"n*log m = {target:.2f};  true B^2 = {B2};  "
              f"LOWER/target = {lbest/target:.3f}" if B2 else "")
    print()
