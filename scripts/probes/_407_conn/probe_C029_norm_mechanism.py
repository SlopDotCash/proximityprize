"""
C029 part 3 (mechanism): is the surplus a CLEAN variety point-count Stepanov can bound, or is
it the norm-divisibility object (= p | N(alpha) for alpha a short root-sum difference) that
the campaign already identified as the BGK/Cheng-house wall?

A surplus tuple is (x,y) in mu_n^{2r} with sum x = sum y mod p but NOT over Z[zeta_n].
Equivalently alpha := sum x - sum y is a NONZERO element of Z[zeta_n] (a sum of <= 2r roots
of unity, each +-zeta^a) with p | alpha in O_K = Z[zeta_n], i.e. the prime p (or a prime above
it) divides alpha. Since p splits completely (p = 1 mod n), p | alpha  <=>  every conjugate
embedding... no: p | alpha in O_K via the chosen prime ideal frak_p above p (the one fixing the
embedding zeta -> g). So p | alpha  <=>  alpha == 0 mod frak_p  <=>  N(alpha) == 0 mod p in the
relevant component. Key: a NONZERO alpha that is a short signed root-sum has BOUNDED house
|alpha|_infty <= 2r, hence |N(alpha)| <= (2r)^{phi(n)} (degree phi(n)=n/2). So p | N(alpha)
requires p <= (2r)^{n/2}  OR  alpha has a large norm with p as a factor.

This is EXACTLY the norm-divisibility wall (memory: arklib-407-largesieve-avgq-refuted,
'bad primes = odd prime factors of {N(alpha)}'). Test:
  - count surplus tuples and verify each corresponds to a nonzero short alpha with p | (its
    reduction at frak_p);
  - confirm the surplus is NONZERO only when p is small enough that short alphas of norm
    divisible by p exist; once p > house-derived ceiling, surplus collapses to 0.
  - check whether the ceiling for surplus>0 is governed by (2r)^{n/2} (the norm/house bound) --
    if so, "Stepanov" buys exactly the norm bound the campaign already has, i.e. it WELDS to
    the same wall and only governs r < ~ (n/2-ish), NOT a new tool for the prize.
"""
import itertools
from sympy import isprime, primitive_root, factorint
import math
from collections import Counter

def primitive_n_root(p, n):
    gr = primitive_root(p)
    g = pow(gr, (p - 1) // n, p)
    assert pow(g, n, p) == 1 and pow(g, n // 2, p) != 1
    return g

def char0_signed_reduce(exps, n):
    half = n // 2
    vec = [0]*half
    for a in exps:
        a %= n
        if a < half: vec[a] += 1
        else: vec[a-half] -= 1
    return tuple(vec)

def has_surplus(n, r, p):
    g = primitive_n_root(p, n)
    powg = [pow(g,a,p) for a in range(n)]
    Np = Counter(); N0 = Counter()
    for exps in itertools.product(range(n), repeat=r):
        Np[sum(powg[a] for a in exps)%p]+=1
        N0[char0_signed_reduce(exps,n)]+=1
    Ep = sum(c*c for c in Np.values()); E0 = sum(c*c for c in N0.values())
    return Ep - E0

def surplus_crossover(n, r):
    """Find, on a GEOMETRIC ladder of proper-subgroup primes p=1 mod n, the largest p at which
    surplus>0 still occurs. Returns (max_p_with_surplus, house=(2r)^{n/2}, top_tested)."""
    half = n//2
    house = (2*r)**half
    max_p = 0
    top = 0
    # geometric ladder: ~ at each scale pick one proper-subgroup prime
    scale = float(n + 1)
    while scale < min(house*4, 5e8):
        target = int(scale)
        p = target - (target % n) + 1
        tries = 0
        while not (isprime(p) and (p-1)%n==0) and tries < 5000:
            p += n; tries += 1
        if isprime(p) and (p-1)%n==0:
            top = p
            if has_surplus(n, r, p) > 0:
                max_p = p
        scale *= 1.8
    return max_p, house, top

def run():
    print("C029 mechanism: largest proper-subgroup prime p with NONZERO surplus vs house (2r)^{n/2}")
    print("If max_p_with_surplus scales with the HOUSE/norm ceiling, the 'Stepanov point-count'")
    print("welds to the EXISTING norm-divisibility wall (no new reach).\n")
    print(f"  {'n':>3} {'r':>2} {'phi=n/2':>7} {'house=(2r)^(n/2)':>20} {'max_p w/ surplus':>17} {'top_tested':>12}")
    for n in (8, 16):
        for r in (2, 3, 4):
            mp, house, top = surplus_crossover(n, r)
            print(f"  {n:>3} {r:>2} {n//2:>7} {house:>20} {mp:>17} {top:>12}", flush=True)
    print()
    print("INTERPRETATION: surplus>0 needs a nonzero short signed root-sum alpha with p | N(alpha).")
    print("For r < n/2 the house (2r)^{n/2} is large => such primes exist up to ~house^{1/?}, but")
    print("the prize prime p ~ n^beta (beta<=5) with n=2^30 has house (2r)^{2^29} >> p ALWAYS for")
    print("operative r, so the norm bound is VACUOUS at the prize (a short alpha CAN have a large")
    print("prime factor) -- the same Cheng-house/largesieve wall the campaign documents.")

if __name__ == "__main__":
    run()
