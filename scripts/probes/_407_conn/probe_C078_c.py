# C078 part C: pin the EXACT structural relationship.
# offdiag E2 = E2 - (2|G|^2 - |G|). Observed offdiag/|G| = n - 2 exactly.
# So offdiag = |G|*(|G|-2) = n^2 - 2n.  Test this and decompose its source.
#
# Also: the connection asserts the F4 list-LB n^{(k+1)/2} is "the F4 IMAGE of the E>=|G|^2
# energy forcing". Test whether at general j, the supply floor C(n/2,j) coincides with any
# energy/moment lower bound at r=j. The moment identity is sum_b |eta_b|^{2r} = q E_r.
#  - F4 supply floor:  zero-sum (2j)-SETS >= C(n/2, j)
#  - F2/F5 moment LB:  from E_r >= (trivial diag, ~ r! |G|^r), the worst period >~ sqrt(|G|) ONLY.
# Key test: does the energy/moment route EVER give a period lower bound stronger than sqrt n,
# i.e. does the supply floor C(n/2,j)=Theta(n^j) translate into a period bound > sqrt n? NO,
# because the moment LB on the WORST period saturates at sqrt|G| for all r (max-vs-sum gap).

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
    G=[]; x=1
    for _ in range(n):
        G.append(x); x=(x*h)%q
    return sorted(set(G))

def Er(G, q, r):
    sums = Counter()
    for tup in itertools.product(G, repeat=r):
        sums[sum(tup)%q]+=1
    return sum(c*c for c in sums.values())

print("Test offdiag E2 = n^2 - 2n exactly:")
for n in [8,16,32,64]:
    q = find_subgroup_prime(n)
    G = subgroup(q,n)
    e2 = Er(G,q,2)
    off = e2 - (2*n*n - n)
    print(f"  n={n:>3}: offdiag={off}, n^2-2n={n*n-2*n}, match={off==n*n-2*n}")

print()
print("=== The decisive question: does the F4 supply floor give a BETTER period bound? ===")
print("F2/F5 worst-period LB:  ||eta_b||^2 >= (q E_r - |G|^{2r}) / (q|G|^{?} ...) -> saturates at |G|.")
print("Compute the actual worst-period LB the 4th-moment gives, and what r->larger gives:")
for n in [8,16,32]:
    q = find_subgroup_prime(n)
    G = subgroup(q,n)
    # 4th moment LB on max ||eta_b||^2 over b != 0:
    #   sum_{b!=0} |eta_b|^4 <= (max||eta_b||^2) * sum_{b!=0}|eta_b|^2
    #   sum_{b!=0}|eta_b|^2 = q|G| - |G|^2 ; sum_{b!=0}|eta_b|^4 = q E2 - |G|^4
    E2v = Er(G,q,2)
    num = q*E2v - n**4
    den = q*n - n*n
    lb_sq = num/den
    print(f"  n={n:>3} q={q}: 4th-moment worst-period^2 LB = {lb_sq:.2f},  |G|={n}, sqrt|G|={n**0.5:.2f}, LB/|G|={lb_sq/n:.3f}")
    # what about 6th moment? E3 -> stronger?
    E3v = Er(G,q,3)
    # sum_{b!=0}|eta_b|^6 <= (max||^2)^2 * sum_{b!=0}|eta_b|^2 ... actually use:
    # (max^2)^2 >= (sum|eta|^6 - |G|^6)/(sum|eta|^2 - ... ) ; cruder. Just show E3 ~ r!|G|^r diag.
    print(f"        E2={E2v} (~2!|G|^2={2*n*n}?), E3={E3v} (~3!|G|^3={6*n**3}?) -> diag dominated")
