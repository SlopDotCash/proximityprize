#!/usr/bin/env python3
"""
#466 Lane L1 — mixed-profile top-fit arithmetic at the z = n endpoint.

Decides numerically whether the named top-fit inequalities
  LowMixedChooseProfileTopSumsFit / FullMixedChooseProfileTopSumsFit
  FieldPowMixedProfileTopFit    / FieldPowFullMixedProfileTopFit
(ArkLib/Data/CodingTheory/ProximityGap/LineListAppearanceFiberMixedProfileFit.lean)
are satisfiable by ANY coarse budget Mcoarse that is simultaneously compatible with the
downstream fiber budget
  UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits a B Mcoarse
(LineListAppearanceFiber.lean:728-739) at prize-shaped parameters.

The exact Lean arithmetic (natural subtraction throughout):

  TOP SUM (z = n endpoint):
    S(t) = sum_{r=0}^{a-1} C(n - t, r - t) * (Mexact(r) if r < k else 1)
  FIELD-POWER Mexact:
    Mexact(r) = q * C(n, a - r) * q^(k -. a)      (k -. a = 0 in-window since a > k)
  TOP FIT:   S(t) <= Mcoarse(t)   for all t < a (and t < k in the "low" form)

  FIBER FIT (necessary single-term consequence, direction with exactly z zeros,
  z >= a, support s = n - z, all z in [a, n] realizable):
    C(z, t) * Mcoarse(t) * floor((n - z)/(a - t)) <= B     for every t < a

  WELD BUDGET: B <= eps* * q  (eps* = 2^-128); task shape also B ~ rho*n.

Regime: rho in {1/2, 1/4, 1/8, 1/16}, n = 2^mu (mu = 4..12 exact, mu = 30 Stirling),
k = rho*n, in-window agreement a in (rho*n, sqrt(rho)*n)  [delta = 1 - a/n in the
prize window (1 - sqrt(rho), 1 - rho - Theta(1/log n))], q ~ n^4 and q ~ n*2^128
(real primes q = 1 mod n).

Output: for each shape, the forced lower bound on Mcoarse(t0) from the top fit
(total sum, the exact field-power term r = t0, and the Mexact-INDEPENDENT high-
singleton floor sum_{k<=r<a} C(n-t0, r-t0)), the fiber-budget cap on Mcoarse(t0),
the violation factor in bits, and which summand binds.
"""

import math
import random
import sys

EPS_STAR_LOG2 = 128  # eps* = 2^-128


# ---------------------------------------------------------------- primality
def is_probable_prime(m: int, rounds: int = 40) -> bool:
    if m < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % p == 0:
            return m == p
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    rng = random.Random(0xA466)
    for _ in range(rounds):
        x = pow(rng.randrange(2, m - 1), d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def prime_1_mod_n_at_least(n: int, lo: int) -> int:
    m = (lo - 1 + n - 1) // n  # smallest m with m*n + 1 >= lo
    m = max(m, 1)
    while True:
        q = m * n + 1
        if is_probable_prime(q):
            return q
        m += 1


# ---------------------------------------------------------------- exact core
def nat_sub(x: int, y: int) -> int:
    return x - y if x >= y else 0


def top_sum_terms(n: int, a: int, k: int, q: int, t: int):
    """Exact Lean summands of fieldPowMixedProfileCardSum(n, a, k, z=n, t)."""
    e = nat_sub(k, a)
    terms = []
    for r in range(a):
        c = math.comb(nat_sub(n, t), nat_sub(r, t))
        w = q * math.comb(n, nat_sub(a, r)) * q ** e if r < k else 1
        terms.append(c * w)
    return terms


def high_floor(n: int, a: int, k: int, t: int) -> int:
    """Mexact-independent part of S(t): sum over high profiles r in [k, a)."""
    return sum(math.comb(nat_sub(n, t), nat_sub(r, t)) for r in range(k, a))


def fiber_cap(n: int, a: int, t: int, B: int):
    """Max Mcoarse(t) allowed by the single-term fiber constraint, tightest over
    realizable z in [a, n]. Returns (cap, z_binding) or (None, None) if no z gives a
    nonzero coefficient (constraint vacuous at this t)."""
    best = None
    zbest = None
    for z in range(a, n + 1):
        coeff = math.comb(z, t) * ((n - z) // (a - t))
        if coeff >= 1:
            cap = B // coeff
            if best is None or cap < best:
                best, zbest = cap, z
    return best, zbest


def lg(x) -> float:
    if x <= 0:
        return float("-inf")
    return math.log2(x)


# ---------------------------------------------------------------- exact scan
def scan_exact():
    print("=" * 100)
    print("EXACT SCAN  mu = 4..12  (all integer arithmetic; Lean natural-subtraction semantics)")
    print("=" * 100)
    print("Columns: t0 = max(0, 2a-n)  [first t with nonzero z=a fiber coefficient; t0 < k checked]")
    print("  S_fp    = full field-power top sum S(t0)   (forced lower bd on Mcoarse(t0))")
    print("  E_fp    = exact same-profile term r=t0:  q*C(n, a-t0)")
    print("  S_high  = Mexact-INDEPENDENT high-singleton floor  sum_{k<=r<a} C(n-t0, r-t0)")
    print("  cap     = fiber-budget cap on Mcoarse(t0)  (tightest single term over z in [a,n])")
    print("  verdict = HOLD iff S_fp <= cap  (joint satisfiability of TopFit + FiberFits)")
    print()
    n_fail = n_hold = 0
    worst_min_gap = None  # smallest violation seen (in bits)
    for rho_num, rho_den in ((1, 2), (1, 4), (1, 8), (1, 16)):
        rho = rho_num / rho_den
        for mu in range(4, 13):
            n = 2 ** mu
            k = n * rho_num // rho_den
            if k < 1:
                continue
            sq = math.sqrt(rho)
            a_hi = math.floor(sq * n)
            if a_hi * a_hi == rho * n * n:  # a/n = sqrt(rho) is the window EDGE; step inside
                a_hi -= 1
            a_lo = k + 2  # first level where direction-spread discriminates (round-1)
            a_mid = round(n * (rho + sq) / 2)
            a_set = sorted({a for a in (a_lo, a_mid, a_hi) if k < a <= a_hi and a <= n})
            q4 = prime_1_mod_n_at_least(n, n ** 4)
            qB = prime_1_mod_n_at_least(n, n * 2 ** EPS_STAR_LOG2)
            for a in a_set:
                t0 = max(0, 2 * a - n)
                assert t0 < a
                if t0 >= k:
                    print(f"rho=1/{rho_den} mu={mu} a={a}: t0={t0} >= k={k} -- no low-profile "
                          f"t with nonzero z=a coefficient (SKIP, would need z>a analysis)")
                    continue
                terms = None
                for (q, qname) in ((q4, "q~n^4"), (qB, "q~n*2^128")):
                    terms = top_sum_terms(n, a, k, q, t0)
                    S = sum(terms)
                    r_bind = max(range(a), key=lambda r: terms[r])
                    E = q * math.comb(n, a - t0)
                    Sh = high_floor(n, a, k, t0)
                    for (B, bname) in ((max(1, k), "B=rho*n"),
                                       (q // 2 ** EPS_STAR_LOG2, "B=eps*q")):
                        cap, zb = fiber_cap(n, a, t0, B)
                        if cap is None:
                            print(f"rho=1/{rho_den} mu={mu} n={n} a={a} {qname} {bname}: "
                                  f"fiber constraint VACUOUS at t0={t0} (unexpected)")
                            continue
                        hold = S <= cap
                        n_hold += hold
                        n_fail += (not hold)
                        gap = lg(S) - lg(max(cap, 1))
                        if not hold and (worst_min_gap is None or gap < worst_min_gap[0]):
                            worst_min_gap = (gap, rho_den, mu, a, qname, bname)
                        print(f"rho=1/{rho_den:<2} mu={mu:<2} n={n:<5} k={k:<4} a={a:<5} "
                              f"t0={t0:<3} {qname:<10} {bname:<8} "
                              f"lg S_fp={lg(S):9.1f}  lg E_fp={lg(E):9.1f}  "
                              f"lg S_high={lg(Sh):9.1f}  lg cap={lg(max(cap,1)):7.1f} "
                              f"(cap={cap}, z*={zb})  bind r={r_bind}"
                              f"{' (=t0 exact)' if r_bind == t0 else ''}  "
                              f"[{'HOLD' if hold else 'FAIL by ' + format(gap, '.0f') + ' bits'}]")
            print()
    print(f"TOTALS: FAIL={n_fail}  HOLD={n_hold}")
    if worst_min_gap:
        g, rd, mu, a, qn, bn = worst_min_gap
        print(f"Smallest violation: {g:.1f} bits at rho=1/{rd}, mu={mu}, a={a}, {qn}, {bn}")
    print()


# ------------------------------------------------------- Mexact-independent kill
def scan_mexact_independent():
    print("=" * 100)
    print("Mexact-INDEPENDENT kill (holds for EVERY exact budget Mexact, even Mexact == 0):")
    print("  TopFit forces Mcoarse(t0) >= C(n - t0, (a-1) - t0)   [high singleton r = a-1;")
    print("  needs only k <= a-1, i.e. the in-window fact a > k]")
    print("  FiberFits forces Mcoarse(t0) <= B  (z = a direction, coefficient >= 1)")
    print("  => joint UNSAT whenever B < C(n - t0, a - 1 - t0).")
    print("=" * 100)
    for rho_num, rho_den in ((1, 2), (1, 4), (1, 8), (1, 16)):
        rho = rho_num / rho_den
        for mu in (4, 8, 12):
            n = 2 ** mu
            k = n * rho_num // rho_den
            sq = math.sqrt(rho)
            a = round(n * (rho + sq) / 2)
            if a <= k + 1:
                a = k + 2
            if a > math.floor(sq * n):
                continue
            t0 = max(0, 2 * a - n)
            if t0 >= k:
                continue
            floor_high = math.comb(n - t0, a - 1 - t0)
            print(f"rho=1/{rho_den:<2} mu={mu:<2} n={n:<5} k={k:<4} a={a:<5} t0={t0:<3} "
                  f"lg C(n-t0, a-1-t0) = {lg(floor_high):10.1f}   vs  lg(B=rho*n) = "
                  f"{lg(max(1, k)):5.1f}   UNSAT margin = {lg(floor_high)-lg(max(1,k)):.1f} bits")
    print()


# ---------------------------------------------------------------- mu=30 Stirling
def lg_comb(n: float, m: float) -> float:
    if m < 0 or m > n:
        return float("-inf")
    return (math.lgamma(n + 1) - math.lgamma(m + 1) - math.lgamma(n - m + 1)) / math.log(2)


def scan_asymptotic():
    print("=" * 100)
    print("ASYMPTOTIC mu = 30 (Stirling / lgamma, log2 units)  n = 2^30, q ~ n*2^128")
    print("=" * 100)
    n = 2 ** 30
    lq = math.log2(n) + EPS_STAR_LOG2  # q ~ n * 2^128
    for rho_num, rho_den in ((1, 2), (1, 4), (1, 8), (1, 16)):
        rho = rho_num / rho_den
        k = n // rho_den
        sq = math.sqrt(rho)
        for aname, afrac in (("a=k+2~rho*n", rho + 2 / n),
                             (("a=mid"), (rho + sq) / 2),
                             (("a~sqrt(rho)n"), sq - 1 / n)):
            a = afrac * n
            t0 = max(0.0, 2 * a - n)
            if t0 >= k:
                continue
            lg_E = lq + lg_comb(n, a - t0)                    # exact field-power term r=t0
            lg_high = lg_comb(n - t0, (a - 1) - t0)           # Mexact-independent floor
            lg_B_rho = math.log2(rho * n)
            lg_B_weld = lq - EPS_STAR_LOG2                    # eps* * q  ~ n
            print(f"rho=1/{rho_den:<2} {aname:<14} a/n={afrac:.4f} t0/n={t0/n:.4f}  "
                  f"lg E_fp={lg_E/1e6:8.2f}M  lg S_high>={lg_high/1e6:8.2f}M  "
                  f"lg B(rho*n)={lg_B_rho:5.1f}  lg B(eps*q)={lg_B_weld:5.1f}   "
                  f"=> FAIL by ~{lg_high/1e6:.1f} MILLION bits (Mexact-indep) / "
                  f"{lg_E/1e6:.1f}M bits (field-pow)")
    print()
    print("Threshold reading: joint satisfiability of (FieldPow)TopFit + FiberFits requires")
    print("  B >= q            (field-power route; weld gives B <= eps* * q = q/2^128), and")
    print("  B >= C(n, a-1)    (ANY-Mexact route; ~2^(n*H(a/n)) >> any polynomial budget).")
    print("Both are impossible at every prize shape: the z=n endpoint contraction is DEAD.")


if __name__ == "__main__":
    random.seed(0x466)
    scan_exact()
    scan_mexact_independent()
    scan_asymptotic()
    print("done.")
