"""
C018 probe: I_infty(delta) is the q-independent stratified census; delta* = I_infty^{-1}(n)
            -- but ONLY above the resultant threshold p > (2^mu)^{2^{mu-1}}.

Claims to test (prize regime: dyadic mu_n, n=2^mu PROPER subgroup of F_q*, q prime =1 mod n,
q ~ n^beta with beta ~ 4-5, n << sqrt(q)):

 (A) census_card_eq_stratified: above p > (2^mu)^{2^{mu-1}}, the exact bad-scalar count
     equals I_infty(1 - r/2^mu) = sum_{j feasible} 2^{r-2j} * C(2^{mu-1}, r-2j),
     a function of (mu, r) ONLY (q-independent).

 (B) PRIZE IS BELOW THRESHOLD: p ~ n^beta is astronomically below (2^mu)^{2^{mu-1}}.

 (C) BELOW threshold (prize regime), the actual char-p census DIFFERS from I_infty
     (extra mod-p collisions) -- so I_infty is the char-0/large-p ENVELOPE only.

We compute, for small mu (mu=3,4 -> n=8,16) and small r:
  - I_infty(mu, r)            (the q-independent stratified census formula)
  - census_p(mu, r)           (exact #distinct r-subset subgroup sums in F_p) for several
                              primes p = 1 mod n, sweeping from prize-scale up.
  - the threshold (2^mu)^{2^{mu-1}}.

We use n=8 (mu=3): threshold = 8^4 = 4096 -- small enough to actually cross.
And n=16 (mu=4): threshold = 16^8 = 2^32 ~ 4.3e9 -- to show prize-scale primes (n^4 ~ 65536)
sit below it AND the census there differs.

Exact integer arithmetic only.
"""

from math import comb
from itertools import combinations
import sys


def feas_set(half, r):
    # j with: r - 2j >= 0  and  r - j <= half   (feasibility from the Lean: |C0 u C1| = r-j <= n=half)
    js = []
    for j in range(0, r // 2 + 1):
        if (r - 2 * j) >= 0 and (r - j) <= half:
            js.append(j)
    return js


def I_infty(mu, r):
    """Stratified q-independent census: sum_j 2^{r-2j} * C(2^{mu-1}, r-2j) over feasible j."""
    half = 2 ** (mu - 1)
    total = 0
    for j in feas_set(half, r):
        total += (2 ** (r - 2 * j)) * comb(half, r - 2 * j)
    return total


def find_primitive_root_of_order(p, order):
    """Find g in F_p* with multiplicative order exactly `order` (order | p-1 required).

    Efficient: g has order exactly `order` iff g^order==1 and for every prime divisor ell
    of `order`, g^{order/ell} != 1. Here order = 2^mu, so the only prime is 2: it suffices
    that g^order==1 and g^{order/2} != 1. We build such a g from a random base via
    h^{(p-1)/order} and accept if its order/2 power != 1; loop over bases.
    """
    if (p - 1) % order != 0:
        return None
    cof = (p - 1) // order
    for base in range(2, p):
        g = pow(base, cof, p)
        if g == 1:
            continue
        # order divides `order` by construction; exact iff g^{order/2} != 1
        if pow(g, order // 2, p) != 1:
            return g
    return None


def census_p(p, mu, r):
    """Exact number of distinct sums of r-element subsets of the order-2^mu subgroup in F_p."""
    n_sub = 2 ** mu
    g = find_primitive_root_of_order(p, n_sub)
    if g is None:
        return None
    elems = [pow(g, i, p) for i in range(n_sub)]
    sums = set()
    for S in combinations(elems, r):
        s = 0
        for x in S:
            s = (s + x) % p
        sums.add(s)
    return len(sums)


def primes_one_mod_n(n, lo, hi, count):
    """Return up to `count` primes p with p = 1 mod n in [lo, hi]."""
    def is_prime(x):
        if x < 2:
            return False
        if x % 2 == 0:
            return x == 2
        i = 3
        while i * i <= x:
            if x % i == 0:
                return False
            i += 2
        return True
    out = []
    # start at smallest p = 1 mod n >= lo
    start = lo + ((n - (lo - 1) % n) % n)
    if (start - 1) % n != 0:
        start = ((lo // n) + 1) * n + 1
    p = start
    while p <= hi and len(out) < count:
        if (p - 1) % n == 0 and is_prime(p):
            out.append(p)
        p += n
    return out


def run_case(mu, r_list, prime_specs):
    n = 2 ** mu
    threshold = n ** (2 ** (mu - 1))
    print(f"\n===== mu={mu}  n=2^mu={n}  resultant threshold (2^mu)^(2^(mu-1)) = {n}^{2**(mu-1)} = {threshold} =====")
    for r in r_list:
        Ii = I_infty(mu, r)
        print(f"\n  r={r}:  I_infty(mu,r) = {Ii}   (feasible j = {feas_set(2**(mu-1), r)})")
        for (label, p) in prime_specs:
            c = census_p(p, mu, r)
            if c is None:
                print(f"      {label} p={p:<12}  (no order-{n} element)")
                continue
            rel = "ABOVE thr" if p > threshold else "BELOW thr (prize-like)"
            diff = c - Ii
            match = "==I_infty" if diff == 0 else f"surplus {diff:+d}"
            print(f"      {label:<14} p={p:<12} census={c:<8} {match:<16} [{rel}]")


def main():
    # ---- n = 8 (mu=3): threshold = 8^4 = 4096, crossable. -----
    # Prize-like primes (=1 mod 8, well below 4096) and above-threshold primes (>4096).
    n = 8
    below = [("prize-small", p) for p in primes_one_mod_n(n, 17, 200, 3)]
    above = [("above-thr", p) for p in primes_one_mod_n(n, 4097, 5000, 3)]
    run_case(3, [3, 4, 5], below + above)

    # ---- n = 16 (mu=4): threshold = 16^8 = 2^32 ~ 4.29e9. Prize p ~ n^4..n^5 = 65536..1.05e6,
    #      all FAR below threshold. We CANNOT cross (above-threshold primes ~4.3e9 make
    #      C(16,r) subset enumeration fine but census_p enumeration is cheap; the issue is
    #      whether prize-scale census already differs from I_infty). -----
    n = 16
    prize = [("prize n^4", p) for p in primes_one_mod_n(n, 60000, 80000, 2)]
    prize5 = [("prize n^5", p) for p in primes_one_mod_n(n, 1000000, 1100000, 2)]
    # an above-threshold prime ~ 2^32 + small, =1 mod 16
    above16 = [("above-thr", p) for p in primes_one_mod_n(n, 2**32, 2**32 + 200000, 1)]
    run_case(4, [3, 4], prize + prize5 + above16)


if __name__ == "__main__":
    main()
