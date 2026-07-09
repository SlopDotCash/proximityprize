# C078 part B: decompose E_2(G) and test whether the F2/F5 "diagonal energy" floor
# E(G) >= |G|^2 has the SAME origin (antipodal/diagonal structure) as the F4 antipodal
# binomial floor C(n/2, j) used by the supply lower bound.
#
# E_2(G) = #{(a,b,c,d) in G^4 : a+b = c+d}.
#   Trivial/diagonal solutions: {a,b}={c,d} as multiset -> exactly |G|^2 such
#     (ordered: (a,b,c,d) with (c,d) a permutation of (a,b)); minus the over/under count.
#   The DIAGONAL energy floor in WorstPeriodLowerBound is E(G) >= |G|^2.
#
# The F4 antipodal floor comes from NEGATION symmetry: pairs (x, -x). The diagonal-energy
# floor comes from the trivial a+b=a+b solutions. Question: are these the SAME structure?
#
# Test: in a NEGATION-CLOSED subgroup mu_n (n even, so -1 in mu_n), how much of E_2 comes
# from negation/antipodal structure vs trivial diagonal?

import itertools
from math import comb, isqrt, log
from collections import Counter

def is_prime(m):
    if m < 2: return False
    for p in range(2, isqrt(m)+1):
        if m % p == 0: return False
    return True

def find_subgroup_prime(n, beta_min=4.0, beta_max=5.5):
    lo = int(n**beta_min); hi = int(n**beta_max)
    q = lo - (lo % n) + 1
    if q < lo: q += n
    while q <= hi:
        if is_prime(q) and (q-1) % n == 0 and n < q-1:
            return q
        q += n
    return None

def subgroup(q, n):
    def order(a):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
            if o > q: return None
        return o
    pr = None
    for cand in range(2, q):
        if order(cand) == q-1:
            pr = cand; break
    h = pow(pr, (q-1)//n, q)
    G = []; x = 1
    for _ in range(n):
        G.append(x); x = (x*h) % q
    return sorted(set(G))

def E2(G, q):
    sums = Counter()
    for a in G:
        for b in G:
            sums[(a+b)%q]+=1
    return sum(c*c for c in sums.values())

print(f"{'n':>4} {'q':>9}  {'E2':>8} {'|G|^2':>7} {'2|G|^2-|G|':>11} {'trivialDiag':>11} {'E2-trivial':>11} {'offdiag/|G|':>11}")
for n in [8, 16, 32, 64]:
    q = find_subgroup_prime(n)
    if q is None: continue
    G = subgroup(q, n)
    e2 = E2(G, q)
    # trivial (a+b=c+d with {a,b}={c,d}): ordered count = 2|G|^2 - |G|
    #   (a,b) any (|G|^2), and (c,d) in {(a,b),(b,a)} => 2|G|^2, minus |G| for a=b double count.
    trivial = 2*n*n - n
    offdiag = e2 - trivial
    print(f"{n:>4} {q:>9}  {e2:>8} {n*n:>7} {2*n*n-n:>11} {trivial:>11} {offdiag:>11} {offdiag/n:>11.2f}")

print()
print("Interpretation key:")
print(" - 'trivial/diagonal' E-floor (2|G|^2-|G|) gives ||eta_b||^2 >~ |G|  (the F2/F5 sqrt-n floor).")
print(" - F4 antipodal floor C(n/2,2) counts NEGATION-pair zero-sum SETS, a DIFFERENT object.")
print()
print("=== Does the F4 supply LB (antipodal sets) FEED the F2/F5 period LB (energy)? ===")
print("Period LB needs E2 >= |G|^2 (TRIVIAL diagonal, holds for ANY set, no negation needed).")
print("Supply LB needs C(n/2,j) zero-sum SETS (NEGATION-pairs, needs -1 in subgroup).")
print()
# Test: does the negation/antipodal structure ADD to E2 beyond the trivial diagonal,
# i.e. is the antipodal supply floor a SUBSET of the energy off-diagonal?
# Zero-sum 4-SETS {w,x,y,z} with w+x+y+z=0 give energy solutions a+b=c+d via a=w,b=x,c=-y,d=-z
# only if -y,-z in G. Count antipodal-derived energy contributions.
for n in [8, 16, 32]:
    q = find_subgroup_prime(n)
    if q is None: continue
    G = subgroup(q, n)
    Gset = set(G)
    has_negation = all((q - x) % q in Gset for x in G)
    # zero-sum 4-subsets
    zsq = sum(1 for T in itertools.combinations(G,4) if sum(T)%q==0)
    print(f"n={n:>3} q={q}: -1 in mu_n? {has_negation}  zeroSum4sets={zsq}  C(n/2,2)={comb(n//2,2)}")
