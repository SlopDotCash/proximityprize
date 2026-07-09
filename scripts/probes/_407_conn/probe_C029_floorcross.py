"""
C029 part 2: the decisive prize question.

The connection claims the surplus is a Stepanov point-count, hence O(n^{2r}/p), hence SUB-FLOOR
for the "low-r band", isolating "the genuinely-open mid band r in (beta/2, ln p)".

Two things to settle:

(A) Is the ceiling surplus <= C * n^{2r}/p actually a STEPANOV bound, or just the trivial
    equidistribution heuristic? Test: surplus / (n^{2r}/p) -- if this is ~1 (random) at small p
    and stable, the ceiling is the EXPECTED count under equidistribution, which needs NO Stepanov
    (it follows from |image of sum map| ~ p). Stepanov would only matter if surplus could
    CONCENTRATE far above n^{2r}/p, which is NOT what the connection's target needs.
    => If the ceiling is the equidistribution heuristic, then "Stepanov point-count" is a
       RELABELING, not a new tool: the bound surplus <= E_r^{Fp} <= n^{2r}/p + (concentration)
       is exactly the deep-moment object, and the open part is the CONCENTRATION = char-p
       cancellation = BGK, NOT a clean variety point-count.

(B) Where does surplus cross the floor n^r? The connection wants the "low band" r<beta/2 clean.
    But the operative band for the prize (deep-moment optimum) is r ~ ln q ~ beta*ln n >> beta.
    Confirm: total energy E_r^{Fp} itself crosses (2r-1)!! n^r (the Gaussian/floor) at r~beta,
    and for r>beta the char-p energy is dominated by the surplus = n^{2r}/p term.
    This is the SAME deep-moment wall (memory O389: r_opt ~ ln q, r_max(char0)~2 log_n p = 2beta).
"""
import itertools
from sympy import isprime, primitive_root
import math
from collections import Counter

def primitive_n_root(p, n):
    gr = primitive_root(p)
    g = pow(gr, (p - 1) // n, p)
    assert pow(g, n, p) == 1 and pow(g, n // 2, p) != 1
    return g

def char0_signed_reduce(exps, n):
    half = n // 2
    vec = [0] * half
    for a in exps:
        a %= n
        if a < half: vec[a] += 1
        else: vec[a - half] -= 1
    return tuple(vec)

def energy_counts(n, p, r):
    g = primitive_n_root(p, n)
    powg = [pow(g, a, p) for a in range(n)]
    Np = Counter(); N0 = Counter()
    for exps in itertools.product(range(n), repeat=r):
        Np[sum(powg[a] for a in exps) % p] += 1
        N0[char0_signed_reduce(exps, n)] += 1
    return sum(c*c for c in Np.values()), sum(c*c for c in N0.values())

def double_fact_odd(r):
    # (2r-1)!! = product of odds up to 2r-1
    v = 1
    for k in range(1, 2*r, 2): v *= k
    return v

def run():
    print("=== (A) Is the surplus ceiling the EQUIDISTRIBUTION heuristic? ===")
    print("For fixed (n,r), grow p. Under equidistribution surplus ~ (n^{2r}-E_r^inf)/p * (1+o(1))")
    print("i.e. surplus*p / (n^{2r}-E_r^inf) -> 1 as p grows. (Stepanov NOT needed for this.)\n")
    n = 16; r = 4
    E0_ref = None
    n2r = n**(2*r)
    print(f"  n={n}, r={r}, n^2r={n2r}")
    print(f"  {'p':>12} {'surplus':>10} {'surplus*p/(n2r-E0)':>20}")
    target = int(n**3.0)
    p = target - (target % n) + 1
    found = 0
    while found < 8:
        if p > n+1 and isprime(p) and (p-1) % n == 0:
            Ep, E0 = energy_counts(n, p, r)
            if E0_ref is None: E0_ref = E0
            denom = n2r - E0
            metric = (Ep - E0) * p / denom
            print(f"  {p:>12} {Ep-E0:>10} {metric:>20.4f}")
            found += 1
            p = int(p * 1.7)  # spread the primes geometrically
            p -= p % n; p += 1
        else:
            p += n
    print("  -> if metric ~ const (~1) the ceiling = equidistribution heuristic (no Stepanov).\n")

    print("=== (B) Floor-crossing of the FULL char-p energy E_r^{Fp} vs Gaussian (2r-1)!! n^r ===")
    print("The prize operative r is the deep-moment optimum ~ ln q >> beta; show E_r^{Fp}")
    print("leaves the Gaussian floor at r ~ beta and is then governed by the surplus = n^{2r}/p.\n")
    for n in (8, 16):
        # fix a single proper-subgroup prime at beta~4
        target = int(n**4.0)
        p = target - (target % n) + 1
        while not (isprime(p) and (p-1)%n==0): p += n
        beta = math.log(p, n)
        print(f"  n={n}, p={p}, beta={beta:.2f}; floor model: Gaussian (2r-1)!! n^r")
        print(f"  {'r':>2} {'E_r^Fp':>14} {'(2r-1)!!n^r':>14} {'E_r^inf':>14} {'surplus':>12} {'Ep/Gauss':>9}")
        for r in range(2, 6):
            Ep, E0 = energy_counts(n, p, r)
            gauss = double_fact_odd(r) * n**r
            print(f"  {r:>2} {Ep:>14} {gauss:>14} {E0:>14} {Ep-E0:>12} {Ep/gauss:>9.3f}")
        print()

if __name__ == "__main__":
    run()
