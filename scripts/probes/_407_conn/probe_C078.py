# Probe for connection C078:
#   "The F4 list-LB (n^{(k+1)/2}) and the F2/F5 4th-moment period-LB (sqrt n)
#    are the SAME tower-word floor."
#
# Two reverse (lower) bounds in tree:
#  (A) evenSupply_ge_choose : at rate 2j-1, supply >= C(|R|, j) = C(n/2, j) = Theta(n^j).
#      Underlying: zero-sum-(2j)-subset count of mu_n >= C(n/2, j) (antipodal binomial).
#  (B) exists_period_sq_ge : ||eta_b||^2 (q|G| - |G|^2) >= q E(G) - |G|^4,
#      and E(G) >= |G|^2 (diagonal energy) gives ||eta_b||^2 >~ |G| = n, i.e. ||eta_b|| >~ sqrt n.
#
# The connecting bridge claimed:  sum_b ||eta_b||^{2r} = q * E_r(G),
#  where E_r(G) = #{(a_1..a_r,b_1..b_r) in G^{2r} : sum a_i = sum b_i}  (2r-th additive energy).
#  Equivalently E_r counts ZERO-SUM signed 2r-tuples (a's minus b's).
#
# CLAIM to test exactly (prize regime: proper subgroup mu_n, n=2^mu, large prime q ~ n^beta):
#   1. Verify sum_b |eta_b|^{2r} = q * E_r(G) exactly (the moment identity, the bridge).
#   2. Identify whether the "diagonal energy" floor E(G) >= |G|^2 used by (B)
#      is the SAME combinatorial object as the antipodal binomial floor C(n/2,2) used by (A).
#   3. Quantify both reverse bounds at the SAME r=2 (quadruples) and check whether they
#      produce the SAME numerical floor, or merely both Theta(sqrt n) / Theta(n^j) loosely.

import itertools
from math import comb, isqrt
import cmath

def is_prime(m):
    if m < 2: return False
    for p in range(2, isqrt(m)+1):
        if m % p == 0: return False
    return True

def find_subgroup_prime(n, beta_min=4.0, beta_max=5.5):
    # q prime, q = 1 mod n, q ~ n^beta, mu_n a PROPER subgroup (n < q-1)
    lo = int(n**beta_min); hi = int(n**beta_max)
    q = lo - (lo % n) + 1
    if q < lo: q += n
    while q <= hi:
        if is_prime(q) and (q-1) % n == 0 and n < q-1:
            return q
        q += n
    return None

def subgroup(q, n):
    # mu_n = unique order-n subgroup of F_q^*  (q-1 divisible by n)
    g = None
    for cand in range(2, q):
        # find element of exact order n: take a generator power
        pass
    # Build via: find a primitive root, then take h = pr^((q-1)/n)
    def order(a):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
            if o > q: return None
        return o
    # find primitive root
    pr = None
    for cand in range(2, q):
        if order(cand) == q-1:
            pr = cand; break
    h = pow(pr, (q-1)//n, q)
    G = []
    x = 1
    for _ in range(n):
        G.append(x); x = (x*h) % q
    G = sorted(set(G))
    assert len(G) == n, (len(G), n)
    return G

def additive_energy_r(G, q, r):
    # E_r = #{(a_1..a_r,b_1..b_r) : sum a = sum b mod q}, exact.
    from collections import Counter
    sums = Counter()
    for tup in itertools.product(G, repeat=r):
        sums[sum(tup) % q] += 1
    return sum(c*c for c in sums.values())

def gauss_period_moment_sum(G, q, r):
    # sum_{b in F_q} |eta_b|^{2r}, eta_b = sum_{y in G} e(b*y/q)
    # Use exact: sum_b |eta_b|^{2r} = q * E_r(G) is the claim; here compute LHS numerically.
    total = 0.0
    for b in range(q):
        s = sum(cmath.exp(2j*cmath.pi*(b*y % q)/q) for y in G)
        total += abs(s)**(2*r)
    return total

def zero_sum_2j_count(G, q, j):
    # #{ T subset of G, |T| = 2j, sum T = 0 mod q }  (SET count, the supply object)
    cnt = 0
    for T in itertools.combinations(G, 2*j):
        if sum(T) % q == 0:
            cnt += 1
    return cnt

print(f"{'n':>4} {'q':>9} {'beta':>5}  {'E1':>6} {'E2':>10}  {'|G|^2':>8} {'E2/q-checkid':>14}")
results = []
for n in [8, 16, 32]:
    q = find_subgroup_prime(n)
    if q is None:
        print(f"{n:>4}  no prime"); continue
    beta = __import__('math').log(q)/__import__('math').log(n)
    G = subgroup(q, n)
    E1 = additive_energy_r(G, q, 1)   # = |G| trivially (sum a = sum b with r=1 means a=b)
    E2 = additive_energy_r(G, q, 2)   # 4th additive energy
    # check moment identity for r=2: sum_b |eta_b|^4 == q * E2   (only for small q feasible)
    check = ""
    if q <= 20000:
        lhs = gauss_period_moment_sum(G, q, 2)
        check = f"{lhs/q:.1f} vs {E2}"
    results.append((n, q, beta, E1, E2, n*n, check))
    print(f"{n:>4} {q:>9} {beta:>5.2f}  {E1:>6} {E2:>10}  {n*n:>8}  {check:>14}")

print()
print("=== Comparing the two reverse-bound floors at r=2 (quadruples) ===")
print(f"{'n':>4} {'q':>9}  {'E2(>=|G|^2?)':>14} {'zeroSumQuad':>12} {'C(n/2,2)':>10} {'q*zeroSumQ/E?':>14}")
for n in [8, 16, 32]:
    q = find_subgroup_prime(n)
    if q is None: continue
    G = subgroup(q, n)
    E2 = additive_energy_r(G, q, 2)
    zsq = zero_sum_2j_count(G, q, 2)       # zero-sum 4-SUBSETS (sets), the F4 supply object
    binom = comb(n//2, 2)                   # antipodal floor C(n/2, 2)
    print(f"{n:>4} {q:>9}  {E2:>14} {zsq:>12} {binom:>10}")
