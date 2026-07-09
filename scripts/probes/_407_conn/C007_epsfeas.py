"""
C007 part 3: where (if anywhere) does the all-witness budget reach eps*=2^-128?

budget/p = C(n,r)/r / p.  This is INCREASING in r for r in [2, n/2] (binomials grow).
So the MINIMUM over the pin range is at the smallest r, r=2:
   budget(2)/p = C(n,2)/2 / p ~ n^2/4 / p = 2^{2mu-2} / 2^{beta mu} = 2^{(2-beta)mu - 2}.
For prize n=2^30, beta=4: 2^{-2*30 - 2} = 2^-62.  beta=5: 2^-92.
Neither reaches 2^-128 -- and that is the SMALLEST budget on the whole pin range.
So the all-witness budget NEVER certifies epsMCA <= 2^-128 in the prize regime.
Confirm by direct min-scan over r=2..crossover.
"""
from math import lgamma, log2, log, isqrt
L2 = log(2.0)

def lg_choose(n, k):
    if k < 0 or k > n:
        return float('-inf')
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / L2

def lg_budget(n, r):
    return lg_choose(n, r) - log2(r)

print("Minimum lg(budget/p) over the pin range r in [2, n/2], vs target -128:")
print(f"{'mu':>4} {'beta':>5} {'lgp':>5} {'argmin r':>9} {'min lg(bud/p)':>14} {'reaches -128?':>14}")
for beta in (4, 5):
    for mu in (10, 20, 30):
        n = 2 ** mu
        lgp = beta * mu
        best = (float('inf'), None)
        # scan r=2..min(n/2, 50000); budget monotone increasing so min is at r=2,
        # but scan to be sure (cheap).
        for r in range(2, min(n // 2, 2000)):
            v = lg_budget(n, r) - lgp
            if v < best[0]:
                best = (v, r)
        print(f"{mu:>4} {beta:>5} {lgp:>5} {best[1]:>9} {best[0]:>14.2f} "
              f"{str(best[0] <= -128):>14}")

print()
print("Closed form: budget(2)/p = C(n,2)/2/p ~ 2^{(2-beta)mu-2}.")
print("To reach 2^-128 you need (2-beta)mu - 2 <= -128, i.e. (beta-2)mu >= 126.")
print("With prize mu=30: need beta-2 >= 4.2, i.e. beta >= 6.2.")
print("But prize regime is beta ~ 4-5 (q ~ n^4..n^5). So the all-witness budget")
print("CANNOT reach eps*=2^-128 at the prize point. The crossover r* is irrelevant:")
print("the lower-half budget bound is already too weak (>> 2^-128) at the SMALLEST r.")
print()
print("Equivalently: the all-witness budget is ~ poly(n)/q ~ n^{O(r)}/q (face-2 'O(n)/q'")
print("family, silent at production budget). The C007 crossover bounds where the budget")
print("falls below the antipodal SUPPLY, NOT where it falls below 2^-128.")
