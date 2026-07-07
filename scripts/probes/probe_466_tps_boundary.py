"""probe_466_tps_boundary.py — the typical-prime sieve boundary (essay §2.5, #466 round 1).

CLAIM under test (essay `deltastar-466-essay-novel-mathematics-2026-07-01.md` §2.5):
the "typical prime" wraparound count — total divisibility mass of the relation resultants
spread over the primes of a dyadic window — stays below Wick up to depth r ≈ β and no further,
matching (by an independent argument) the DC-crossover and the moment-exponent threshold.

Model: relations a ∈ {0,±1}^n with ℓ1-norm 2r (r "+1"s and r "−1"s up to sign conventions),
N_a = the nonzero integer invariant (|N_a| ≤ (2r)^{n/2}, the conjugate bound; sharpened
(2w)^{n/4}). Each prime divisor of N_a is ≤ |N_a|, so ω(N_a) ≤ log2|N_a| ≤ (n/2)·log2(2r).
Total mass over the prime window [X, 2X], X = n^β, π-count ≈ X/ln X:

    typicalW(r) ≈ #relations(r) · ω_max / (X / ln X)
    #relations(r) ≈ C(n, r)·C(n−r, r) ≤ n^{2r}/(r!)^2      (choose + and − supports)
    Wick(r)      = (2r−1)!! · n^r

Verdict rule: report r_cross(n, β) = first r where typicalW > Wick; the claim holds if
r_cross ≈ β + O(1) uniformly over n (i.e. the sieve closes exactly the fixed-depth regime
that is already closed, and nothing more).

NOTE this is bookkeeping with the CRUDE upper bound for #relations and ω — i.e. the most
OPTIMISTIC reading for the sieve; if even this crosses at r ≈ β, the boundary claim stands
in the only direction that matters (the sieve cannot reach r ≈ log p ≫ β).
"""
import math

def log_comb(n, k):
    if k < 0 or k > n:
        return float('-inf')
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)

def log_double_fact_odd(r):
    # log (2r-1)!! = lgamma(2r)/... use (2r-1)!! = (2r)!/(2^r r!)
    return math.lgamma(2 * r + 1) - r * math.log(2) - math.lgamma(r + 1)

def analyze(mu, beta):
    n = 2 ** mu
    ln_n = math.log(n)
    X = n ** beta
    ln_X = beta * ln_n
    log_pi = math.log(X) - math.log(ln_X)          # log #primes in window ~ X/lnX
    rows = []
    r_cross = None
    for r in range(2, 200):
        log_rel = log_comb(n, r) + log_comb(n - r, r)      # supports of +s and -s
        log_omega = math.log((n / 2) * math.log2(2 * r))   # ω(N_a) crude cap
        log_typical = log_rel + log_omega - log_pi
        log_wick = log_double_fact_odd(r) + r * ln_n
        crossed = log_typical > log_wick
        if crossed and r_cross is None:
            r_cross = r
        if r <= 12 or (r_cross and r <= r_cross + 2):
            rows.append((r, log_typical / ln_n, log_wick / ln_n, crossed))
        if r_cross and r > r_cross + 2:
            break
    return n, r_cross, rows

print("typical-prime sieve boundary: r_cross vs beta   (log base n units)")
print("=" * 76)
for beta in (3, 4, 4.5, 5, 6):
    print(f"\n--- beta = {beta} ---")
    for mu in (10, 20, 30, 40):
        n, r_cross, rows = analyze(mu, beta)
        print(f"  n = 2^{mu}: r_cross = {r_cross}   (claim: ~ beta + O(1))")
        if mu == 30:
            for (r, t, w, c) in rows:
                mark = "XX" if c else "  "
                print(f"      r={r:3d}  typical~n^{t:7.2f}  Wick~n^{w:7.2f}  {mark}")
print("\nVERDICT rule: claim stands iff r_cross stays within O(1) of beta for all n.")
