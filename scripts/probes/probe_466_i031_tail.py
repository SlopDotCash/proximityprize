#!/usr/bin/env python3
"""probe_466_i031_tail.py -- LANE L4(B) (#466): is the I031 dilation-quotient entropy
reduction exploitable at the TAIL/union-bound input (Lamzouri-style), given that it is
proven cosmetic at the MOMENT input (i031_chaining_cosmetic, Frontier/_AssaultV2_I031Chaining.lean:
the quotient sum = full sum / n, and n^(1/2r) -> 1 at chaining depth)?

SETUP.  |eta_b| is exactly mu_n-dilation invariant, so M = max_{b!=0}|eta_b| is a max over
m = (p-1)/n orbit reps.  Two routes to M from PER-REP inputs:
  UNION route: an input tail/value-distribution bound  #{reps : |eta_rep| > t} <= m*G(t);
               conclude M <= inf{ t : m*G(t) < 1 }.
  MOMENT route: an input moment bound  (1/m) sum_reps |eta_rep|^(2r) <= mu_2r;
               conclude M <= (m * mu_2r)^(1/2r).
"Same input strength" = both consume per-rep moments up to depth r (the recognized-open
A_r <= Wick object).  From depth-r moments the best available tail is Markov:
  #{|eta|>t} <= sum_reps |eta|^(2r) / t^(2r) <= m*mu_2r/t^(2r).

PART 0 (exact identity, the decision core).  Union-with-Markov-tail at depth r gives
  M <= inf{ t : m*mu_2r/t^(2r) < 1 } = (m*mu_2r)^(1/2r)  -- LITERALLY the moment bound.
So at matched input strength the union route is ARITHMETICALLY IDENTICAL to the quotient
moment route; verified below by independent bisection on the tail function vs the closed
form (machine-precision agreement) + one exact-integer instance.

PART 1 (pure finite arithmetic, no primes).  Complex-Wick per-rep input mu_2r = r! sigma^(2r)
(E|g|^2 = sigma^2 complex Gaussian => P(|g|>t) = exp(-t^2/sigma^2), E|g|^(2r) = r! sigma^(2r)).
Grid n = 2^mu, q-size p ~ n^beta, m = n^(beta-1), sigma = sqrt(n).  Quantities (units of sigma):
  t_gauss_quot = sqrt(ln m)          [union over m reps with the FULL Gaussian tail]
  t_gauss_full = sqrt(ln(mn))        [union over all p-1 frequencies, same tail]
  t_mom_quot   = min_r (m  r!)^(1/2r)   at optimal integer depth r*_q
  t_mom_full   = min_r (mn r!)^(1/2r)   at optimal integer depth r*_f
Questions quantified:
  (i)  moments-at-matched-depth vs true-Gaussian-tail union: t_mom_quot / t_gauss_quot -> 1?
  (ii) the entropy factor: t_*_quot / t_*_full vs the predicted sqrt(ln m / ln(mn))
       = sqrt((beta-1)/beta) at fixed beta -- REAL constant factor, identical in BOTH routes?
  (iii) depth relocation: r*_q / r*_f vs (beta-1)/beta -- the required Wick depth drops only
       by the same constant factor; the input stays depth ~ ln m = (1-1/beta) ln p.

PART 2 (real-data sanity, n=16, generic primes p=65617 & 65633, regime-clean, non-Fermat).
  * orbit invariance of |eta| verified to machine precision; m = (p-1)/n reps extracted;
  * per-rep moment wall: A_r = (1/m) sum_reps |eta_rep|^(2r) vs Wick r! sigma^(2r), r = 1..14
    (A_1/Wick_1 = 1 is an exact identity = per-orbit Parseval; the creep above 1 at larger r
    is THE open wall);
  * per-rep tail vs Gaussian: #{reps:|eta|>t} vs m exp(-t^2/sigma^2) on a t-grid;
  * bound stack vs the true M: unconditional empirical (m A_r)^(1/2r), conditional Wick
    (m r!)^(1/2r) sigma, Gaussian-tail union sigma sqrt(ln m), full-index versions.

PRE-REGISTERED DECISION.
  * If PART 0 identity holds (it does, it is an inequality-chain identity) and PART 1 gives
    (i) ratio -> 1, then the union route adds NOTHING over the quotient moment route at
    matched input strength: the entropy reduction is exactly as cosmetic at the tail as at
    the moment -- the log(p/n)/log(p) exponent factor is REAL (constant sqrt((beta-1)/beta)
    at fixed beta) but is already delivered by depth-relocated quotient moments, and the
    required input remains the SAME open per-rep Wick/subgaussian object at depth ~ ln m.
  * PART 2 additionally tests whether the strongest possible tail input (true per-rep
    Gaussian tail) is even TRUE at finite n: if M > sigma sqrt(ln m), the Gaussian-union
    output undershoots reality (the known I031 deterministic->random constant creep), so no
    tail-input variant can close the constant either.

Output: scripts/probes/_out_466_i031_tail.txt
"""
import math

import numpy as np


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a % x == 0:
            continue
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def subgroup_lifts(p: int, n: int):
    m = (p - 1) // n
    for a in range(2, p):
        b = pow(a, m, p)
        if b == 1 or pow(b, n // 2, p) == 1:  # n = 2-power here: order n iff b^(n/2) != 1
            continue
        return sorted(pow(b, j, p) for j in range(n))
    raise RuntimeError


def ln_moment_bound(count_ln: float, r: int) -> float:
    """ln of (count * r!)^(1/2r)  [in units of sigma]."""
    return (count_ln + math.lgamma(r + 1)) / (2 * r)


def optimize_depth(count_ln: float, rcap: int):
    best_r, best = 1, ln_moment_bound(count_ln, 1)
    for r in range(2, rcap + 1):
        v = ln_moment_bound(count_ln, r)
        if v < best:
            best_r, best = r, v
    return best_r, math.exp(best)


def main():
    out = open("scripts/probes/_out_466_i031_tail.txt", "w")
    P = lambda *a: print(*a, file=out)
    P("LANE L4(B) #466 -- I031 Lamzouri tail-union vs moment route (deterministic, no RNG)")

    # ---------------------------------------------------------------- PART 0: exact identity
    P("\n" + "=" * 100)
    P("PART 0 -- union-with-Markov-tail(depth r) == quotient-moment(depth r): exact identity")
    P("  chain: #{reps:|eta|>t} <= sum_reps|eta|^(2r)/t^(2r) <= m*mu_2r/t^(2r);  '<1' <=> t^(2r) > m*mu_2r")
    P("  hence inf{t: union succeeds} = (m*mu_2r)^(1/2r) = the moment bound.  Numeric cross-check:")
    worst = 0.0
    for m in (2 ** 12, 2 ** 24, 2 ** 48):
        for r in (2, 8, 17, 33):
            lnmu = math.lgamma(r + 1)  # Wick, sigma=1 units
            closed = math.exp((math.log(m) + lnmu) / (2 * r))
            lo, hi = 1e-9, 1e9  # bisection on f(t) = ln m + ln mu_2r - 2r ln t = 0
            for _ in range(200):
                mid = math.sqrt(lo * hi)
                if math.log(m) + lnmu - 2 * r * math.log(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            worst = max(worst, abs(math.sqrt(lo * hi) - closed) / closed)
    P(f"  max relative deviation bisection-vs-closed-form over grid: {worst:.2e}  (identity holds)")
    m, r, s2 = 4096, 8, 16
    P(f"  exact-integer instance m={m}, r={r}, sigma^2={s2}: union and moment routes both gate at"
      f" t^(2r) > m*r!*sigma^(2r) = {m*math.factorial(r)*s2**r}  (same integer, same bound)")

    # ---------------------------------------------------------------- PART 1: finite arithmetic
    P("\n" + "=" * 100)
    P("PART 1 -- Wick-input routes, grid over (mu, beta); all t in units of sigma = sqrt(n)")
    P(f"{'mu':>3} {'beta':>4} {'ln m':>7} {'tG_quot':>8} {'tG_full':>8} {'tM_quot':>8} {'r*_q':>5} "
      f"{'tM_full':>8} {'r*_f':>5} {'tMq/tGq':>8} {'quot/full(M)':>12} {'quot/full(G)':>12} "
      f"{'pred sqrt(1-1/b)':>16} {'r*q/r*f':>8}")
    for beta in (3, 4, 6):
        for mu in (4, 8, 16, 24, 32):
            n = 2 ** mu
            ln_m = (beta - 1) * mu * math.log(2.0)
            ln_full = beta * mu * math.log(2.0)
            tGq, tGf = math.sqrt(ln_m), math.sqrt(ln_full)
            rcap = int(8 * ln_full) + 4
            rq, tMq = optimize_depth(ln_m, rcap)
            rf, tMf = optimize_depth(ln_full, rcap)
            P(f"{mu:>3} {beta:>4} {ln_m:>7.2f} {tGq:>8.4f} {tGf:>8.4f} {tMq:>8.4f} {rq:>5} "
              f"{tMf:>8.4f} {rf:>5} {tMq/tGq:>8.4f} {tMq/tMf:>12.4f} {tGq/tGf:>12.4f} "
              f"{math.sqrt(1-1/beta):>16.4f} {rq/rf:>8.4f}")
    P("  matched-depth detail (beta=4): t_mom_quot(r)/t_gauss_quot at r = round(ln m):")
    for mu in (4, 8, 16, 24, 32):
        ln_m = 3 * mu * math.log(2.0)
        r = max(1, round(ln_m))
        P(f"    mu={mu:>2}: r=ln m={r:>3}  ratio = {math.exp(ln_moment_bound(ln_m, r))/math.sqrt(ln_m):.4f}")

    # ---------------------------------------------------------------- PART 2: real data n=16
    P("\n" + "=" * 100)
    P("PART 2 -- real-data sanity, n=16 (generic primes, p >= n^4, p == 1 mod n, non-Fermat)")
    n = 16
    for p in (65617, 65633):
        assert is_prime(p) and (p - 1) % n == 0
        lifts = subgroup_lifts(p, n)
        m = (p - 1) // n
        bs = np.arange(p, dtype=np.float64)
        eta = np.zeros(p, dtype=np.complex128)
        for x in lifts:
            eta += np.exp(2j * math.pi / p * ((bs * x) % p))
        av = np.abs(eta)
        # orbit extraction: canonical rep = min over mu_n of b*x mod p
        B = (np.arange(1, p, dtype=np.int64)[:, None] * np.int64(lifts)[None, :]) % p
        canon = B.min(axis=1)
        reps, first = np.unique(canon, return_index=True)
        assert len(reps) == m
        # invariance check: per-orbit spread of |eta|
        order = np.argsort(canon, kind="stable")
        grp = av[1:][order].reshape(m, n)
        spread = float(np.max(grp.max(axis=1) - grp.min(axis=1)))
        vals = av[1:][first]  # one |eta| per orbit
        sig2 = n * (p - n) / (p - 1)
        sig = math.sqrt(sig2)
        M = float(av[1:].max())
        P(f"\n  p={p}  m={m}  sigma^2=n(p-n)/(p-1)={sig2:.6f}  M={M:.4f}  M/sigma={M/sig:.4f}")
        P(f"  orbit-invariance of |eta|: max within-orbit spread = {spread:.2e}  (machine precision)")
        P(f"  A_1/Wick_1 = {float(np.mean(vals**2))/sig2:.12f}  (exact identity check)")
        P("  per-rep moment wall  A_r/(r! sigma^(2r)):")
        row = []
        for r in range(1, 15):
            Ar = float(np.mean(vals.astype(np.float64) ** (2 * r)))
            row.append(f"r{r}={Ar/(math.factorial(r)*sig2**r):.3f}")
        P("    " + "  ".join(row))
        P("  per-rep tail vs Gaussian:  t/sigma : #{reps:|eta|>t}  vs  m*exp(-t^2/sigma^2)")
        for ts in (2.0, 2.5, 2.883, 3.0, 3.2, M / sig):
            cnt = int(np.sum(vals > ts * sig))
            P(f"    {ts:6.3f} : {cnt:>6}  vs  {m*math.exp(-ts*ts):>10.2f}"
              + ("   <- t = sigma*sqrt(ln m) (Gaussian-union threshold)" if abs(ts - 2.883) < 1e-3 else "")
              + ("   <- t = M (the actual max)" if abs(ts - M / sig) < 1e-9 else ""))
        tGq, tGf = sig * math.sqrt(math.log(m)), sig * math.sqrt(math.log(p - 1))
        P(f"  bound stack vs truth M = {M:.4f}:")
        best_emp, best_emp_r = None, None
        best_wick, best_wick_r = None, None
        for r in range(1, 61):
            te = sig * 0 + (m * float(np.mean(vals.astype(np.float64) ** (2 * r)))) ** (1 / (2 * r))
            tw = sig * math.exp(ln_moment_bound(math.log(m), r))
            if best_emp is None or te < best_emp:
                best_emp, best_emp_r = te, r
            if best_wick is None or tw < best_wick:
                best_wick, best_wick_r = tw, r
        P(f"    unconditional empirical quotient-moment min_r (sum_reps|eta|^2r)^(1/2r)"
          f" = {best_emp:.4f} at r={best_emp_r}  (true bound, ->M)")
        P(f"    conditional Wick quotient-moment  min_r sigma(m r!)^(1/2r) = {best_wick:.4f}"
          f" at r={best_wick_r}   [WOULD-BE bound if A_r<=Wick held]")
        P(f"    Gaussian-tail union (quotient)    sigma sqrt(ln m)        = {tGq:.4f}")
        P(f"    Gaussian-tail union (full index)  sigma sqrt(ln(p-1))     = {tGf:.4f}")
        P(f"    M / [sigma sqrt(ln m)] = {M/tGq:.4f}   (>1 => even the FULL Gaussian-tail input"
          f" undershoots the deterministic truth: the I031 constant creep)")
        rff, tff = optimize_depth(math.log(p - 1.0), 200)
        P(f"    Wick-conditional full-index moment min_r sigma((p-1) r!)^(1/2r) = {sig*tff:.4f}"
          f" at r={rff}; quotient/full gain = {best_wick/(sig*tff):.4f}"
          f" (predicted sqrt(ln m/ln(p-1)) = {math.sqrt(math.log(m)/math.log(p-1.0)):.4f})")

    P("\n" + "=" * 100)
    P("VERDICT lines are in the kb note; the decision inputs above are exact/deterministic.")
    out.close()
    print("done -> scripts/probes/_out_466_i031_tail.txt")


if __name__ == "__main__":
    main()
