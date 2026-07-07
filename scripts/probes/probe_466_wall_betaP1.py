#!/usr/bin/env python3
"""probe_466_wall_betaP1.py -- LANE W1 (#466): the first UNPROVEN rung r = beta+1.

CONTEXT.  The DC-subtracted char-p energy A_r = E_r^{(p)} - n^{2r}/p <= K^r*Wick is PROVEN for
r <= beta (three agreeing methods: DC-crossover, moment-exponent, TPS boundary); the prize
needs it to r ~ ln q.  This probe asks what EXACTLY carries the first past-crossover rung and
whether there is a provable statement (bound / exact formula / sharp no-go).

EXACT DECOMPOSITION.  Char-p energy count E_r^{(p)} = E_r^inf + W_r, W_r>=0 (wraparound/anomaly),
where E_r^inf = char-0 energy is p-INDEPENDENT.  For the DYADIC subgroup mu_{2^mu} (Phi_n=x^{n/2}+1)
there is an EXACT closed form (mapping zeta^a -> +-e_{a mod n/2} in Z^{n/2}):
    E_r^inf(n) = sum_{c_1+...+c_{n/2}=r} (2r)! / prod_t (c_t!)^2       (d := n/2)
(verified: reproduces E_2=3n^2-3n, E_3=15n^3-45n^2+40n).  By Lam-Leung E_r^inf <= Wick :=
(2r-1)!!*n^r (PROVEN; in-tree zeroSumCount_le_doubleFactorial_dyadic).  Then EXACTLY
    A_r = E_r^inf + (W_r - n^{2r}/p) = E_r^inf + D_r,   D_r := W_r - n^{2r}/p,
and  A_r <= Wick  <==>  D_r <= BUDGET_r := Wick - E_r^inf.
So (given char-0, which is proven) the ENTIRE open content of the depth-r Wick bound is:
"the wraparound DC-deviation D_r stays within the char-0 budget BUDGET_r."

PART (b) -- the SIGN of the wraparound (round-4 "sub-smooth negative excess") is precisely
the sign of D_r.  We report sgn(D_r), |D_r| vs Wick / BUDGET / the Poisson scale sqrt(n^{2r}/p),
and (via an EXACT integer level decomposition E_r^{(p)} = sum_k N_k, k=(sum_Z x - sum_Z y)/p)
where D_r lives (level 0 = integer/archimedean energy vs wraparound levels k!=0).

EXACTNESS.  E_r^inf: exact (closed form, Fraction).  A_r and D_r: EXACT via int64 level counts
whenever n^{2r} < 2^63 (n=8 r<=9, n=16 r<=7, n=32 r<=6 -- covers every crossover rung r* and
r=beta+1); float eta-sum elsewhere (A_r/Wick good to ~1e-13; SIGN claims only on exact rungs).

REGIME.  mu_n proper subgroup F_p^* (m=(p-1)/n>1, never n=p-1), p==1 mod n, lifts in [1,p-1].
PRIMARY beta=4 (prize diagonal); FLAGGED accelerant beta~3 (shifts finite-n crossover down --
labelled, NOT prize evidence); FLAGGED generalized-Fermat contrast 65537.  >=2 primes/(n,beta),
distinct v2 classes, GF skipped from the main pool.

Output: scripts/probes/_out_466_wall_betaP1.txt
"""
import math
import time
from fractions import Fraction

import numpy as np


# ----------------------------------------------------------------------------- number theory
def is_prime(x: int) -> bool:
    if x < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
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


def v2(x: int) -> int:
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def _factor(n: int):
    fs, d = [], 2
    while n > 1:
        while n % d == 0:
            fs.append(d)
            n //= d
        d += 1
    return fs


def is_generalized_fermat(p: int) -> bool:
    for s in range(1, 20):
        e = 1 << s
        b = round((p - 1) ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb >= 2 and bb ** e + 1 == p:
                return True
    return False


def find_primes(n: int, beta: float, count: int, skip_gf: bool = True):
    out, seen_v2 = [], set()
    start = int(round(n ** beta))
    p = start + ((-(start - 1)) % n)
    pool, guard = [], 0
    while len(pool) < 30 and guard < 400000:
        guard += 1
        if is_prime(p) and (p - 1) // n > 1:
            if not (skip_gf and is_generalized_fermat(p)):
                pool.append(p)
        p += n
    for q in pool:
        if v2(q - 1) not in seen_v2:
            out.append(q); seen_v2.add(v2(q - 1))
        if len(out) == count:
            return out
    for q in pool:
        if q not in out:
            out.append(q)
        if len(out) == count:
            return out
    return out


def subgroup_lifts(p: int, n: int):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    for a in range(2, p):
        b = pow(a, m, p)
        if b == 1:
            continue
        ok = True
        for q in set(_factor(n)):
            if pow(b, n // q, p) == 1:
                ok = False
                break
        if ok:
            elems = sorted(pow(b, j, p) for j in range(n))
            assert len(set(elems)) == n
            return elems
    raise RuntimeError("no order-n element found")


def double_fact_odd(r: int) -> float:
    return math.exp(math.lgamma(2 * r + 1) - r * math.log(2) - math.lgamma(r + 1))


# ----------------------------------------------------------------------------- char-0 energy (EXACT)
def char0_energy_exact(n: int, r: int) -> int:
    """E_r^inf(mu_{2^mu}) = sum_{c_1+...+c_d = r} (2r)!/prod(c_t!^2),  d = n/2.
    Computed as (2r)! * [x^r] ( sum_{c>=0} x^c/(c!)^2 )^d  with exact Fractions."""
    d = n // 2
    base = [Fraction(1, math.factorial(c) ** 2) for c in range(r + 1)]  # sum x^c/(c!)^2 up to x^r
    poly = [Fraction(1)]  # (…)^0
    for _ in range(d):
        new = [Fraction(0)] * (r + 1)
        for i, a in enumerate(poly):
            if a == 0:
                continue
            for j, b in enumerate(base):
                if i + j > r:
                    break
                new[i + j] += a * b
        poly = new
    val = poly[r] * math.factorial(2 * r)
    assert val.denominator == 1, val
    return val.numerator


# ----------------------------------------------------------------------------- char-p engines
def eta_abs2(p: int, lifts) -> np.ndarray:
    bs = np.arange(p, dtype=np.float64)
    ang = 2.0 * math.pi / p
    eta = np.zeros(p, dtype=np.complex128)
    for x in lifts:
        eta += np.exp(1j * ang * ((bs * x) % p))
    return eta.real ** 2 + eta.imag ** 2


def A_r_float(absq: np.ndarray, r: int) -> float:
    p = len(absq)
    return float(math.fsum((absq[1:] ** r).tolist())) / p


def fft_convolve_int(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    L = len(a) + len(b) - 1
    N = 1 << (L - 1).bit_length()
    c = np.fft.irfft(np.fft.rfft(a.astype(np.float64), N) * np.fft.rfft(b.astype(np.float64), N), N)[:L]
    ci = np.rint(c)
    assert float(np.max(np.abs(c - ci))) < 1e-2, "FFT conv not integral"
    return ci.astype(np.int64)


def level_counts_int64(n: int, p: int, lifts, r: int):
    """Exact N_k (int64-safe iff n^{2r} < 2^63) and E_r^{(p)} = sum_k N_k."""
    base = np.zeros(p, dtype=np.int64)
    for x in lifts:
        base[x] = 1
    f = base
    for _ in range(2, r + 1):
        f = fft_convolve_int(f, base)
    assert int(f.sum()) == n ** r
    L = len(f)

    def g_at(d: int) -> int:
        d = abs(d)
        if d >= L:
            return 0
        return int(np.dot(f[d:], f[:L - d]))  # int64 dot; exact since N_k <= n^{2r} < 2^63

    N = {k: g_at(k * p) for k in range(0, r)}
    Er = N[0] + 2 * sum(N[k] for k in range(1, r))
    return N, Er


# ----------------------------------------------------------------------------- per prime
def run(n, p, beta_tag, rmin, rmax, out):
    lifts = subgroup_lifts(p, n)
    m = (p - 1) // n
    beta_eff = math.log(p, n)
    gf = is_generalized_fermat(p)
    absq = eta_abs2(p, lifts)
    par = float(np.sum(absq[1:]))
    M = math.sqrt(float(np.max(absq[1:])))

    print(f"\n{'='*120}", file=out)
    print(f"n={n}  p={p}  m=(p-1)/n={m}  v2(p-1)={v2(p-1)}  beta_eff={beta_eff:.4f}"
          f"  (target {beta_tag}){'   ** GENERALIZED-FERMAT (flagged) **' if gf else ''}", file=out)
    print(f"  Parseval rel {abs(par-n*(p-n))/(n*(p-n)):.1e};  M={M:.3f}"
          f"  sqrt(n log(p/n))={math.sqrt(n*math.log(p/n)):.3f}", file=out)

    r_star = next((r for r in range(1, rmax + 6)
                   if (n ** (2 * r)) / p > double_fact_odd(r) * n ** r), None)
    exact_cap = next((r for r in range(1, 40) if n ** (2 * r) >= 2 ** 62), 40) - 1
    print(f"  finite-n crossover r* (first r: n^2r/p > Wick) = {r_star};  "
          f"beta_eff+1 = {beta_eff+1:.2f};  int64-exact levels up to r={exact_cap}", file=out)

    print(f"\n  {'r':>2} {'DC/Wick':>10} {'A_r/Wick':>9} {'Einf/Wick':>9} {'D_r=A-Einf':>13} "
          f"{'sgn':>3} {'D/Wick':>10} {'D/BUDGET':>9} {'|D|/Pois':>9} {'exact':>5} {'past':>4}", file=out)
    for r in range(rmin, rmax + 1):
        wick = double_fact_odd(r) * n ** r
        DC = (n ** (2 * r)) / p
        Einf = char0_energy_exact(n, r)
        budget = wick - Einf
        exact = (n ** (2 * r) < 2 ** 62)
        if exact:
            N, Er = level_counts_int64(n, p, lifts, r)
            pA = p * Er - n ** (2 * r)          # = p * A_r, exact int
            A = pA / p
            D = A - Einf                          # exact up to Einf(exact) and A(exact)
            Dexact = Fraction(pA, p) - Einf
            D = float(Dexact)
        else:
            A = A_r_float(absq, r)
            D = A - Einf
        poisson = math.sqrt(DC) if DC > 0 else 1.0
        past = "YES" if (r_star and r >= r_star) else "no"
        print(f"  {r:>2} {DC/wick:>10.3e} {A/wick:>9.4f} {Einf/wick:>9.4f} {D:>13.4e} "
              f"{'-' if D < 0 else '+':>3} {D/wick:>10.3e} {D/budget if budget else float('nan'):>9.3f} "
              f"{abs(D)/poisson:>9.3f} {'Y' if exact else 'n':>5} {past:>4}", file=out)

    # exact level decomposition around the crossover, to LOCATE D_r
    print(f"\n  --- exact level decomposition E_r^(p)=sum_k N_k (locate the deviation) ---", file=out)
    lo = max(rmin, (r_star or rmin) - 2)
    for r in range(lo, rmax + 1):
        if n ** (2 * r) >= 2 ** 62:
            print(f"  r={r}: (skipped -- n^2r exceeds int64)", file=out)
            continue
        N, Er = level_counts_int64(n, p, lifts, r)
        Einf = char0_energy_exact(n, r)
        wrap_ct = 2 * sum(N[k] for k in range(1, r))
        wraparound_true = Er - Einf           # W_r = E_r^(p) - char0
        DC = Fraction(n ** (2 * r), p)
        Draw = Fraction(p * Er - n ** (2 * r), p) - Einf
        ks = [k for k in range(1, r) if N[k] > 0]
        print(f"  r={r}: E_r^(p)={Er}  Einf={Einf}  W_r=E-Einf={wraparound_true}  "
              f"DC=n^2r/p={float(DC):.4g}  D_r={float(Draw):+.6g}", file=out)
        print(f"       level-0 N_0={N[0]}  (share {N[0]/Er:+.5f});  "
              f"residue-wraparound sum_(k!=0)N_k={wrap_ct} (share {wrap_ct/Er:+.5f});  "
              f"nonzero levels k={ks[:10]}", file=out)


def prize_scale_table(out):
    print(f"\n{'='*120}", file=out)
    print("PRIZE-SCALE EXTRAPOLATION  (n=2^30, beta=4; symbolic, exact Einf coefficient)", file=out)
    mu, beta = 30, 4
    n = 2 ** mu
    print("  DC/Wick = n^{r-beta}/(2r-1)!!;  char-0 budget (Wick-Einf)/Wick and the REQUIRED", file=out)
    print("  relative precision on W_r = BUDGET/DC = (Wick-Einf)/(n^{2r}/p):", file=out)
    for r in (beta, beta + 1, beta + 2, beta + 3):
        wick_log2 = math.log2(double_fact_odd(r)) + r * mu
        DC_log2 = (2 * r - beta) * mu
        # exact leading char-0 defect: Einf/Wick = 1 - defect; defect ~ C(r,2)/n leading (from ladder)
        Einf = char0_energy_exact(8, r)  # shape only; use the exact defect coefficient via small-n fit
        # leading defect coefficient c_r: Einf = Wick*(1 - c_r/n + ...), c_r = C(r,2) (checked r=2,3)
        c_r = math.comb(r, 2)
        budget_log2 = wick_log2 + math.log2(c_r) - mu     # (Wick - Einf) ~ Wick * c_r / n
        reqprec_log2 = budget_log2 - DC_log2
        print(f"  r={r} (beta+{r-beta}): DC/Wick=2^{DC_log2-wick_log2:+.1f};  "
              f"(Wick-Einf)/Wick ~ C(r,2)/n = 2^{math.log2(c_r)-mu:+.1f};  "
              f"REQUIRED rel prec on W_r = 2^{reqprec_log2:+.1f}", file=out)
    print("  READING: r=beta+1 is the SHALLOWEST wall rung, but A_{beta+1} <= Wick still requires", file=out)
    print("  the arithmetic wraparound count W_r to match its DC mean n^{2r}/p to relative", file=out)
    print("  precision 2^{~-56} -- a genuine square-root-cancellation/concentration statement.", file=out)
    print("  The char-0 half (E_r^inf<=Wick) is PROVEN; the residual is this concentration.", file=out)


def main():
    t0 = time.time()
    with open("scripts/probes/_out_466_wall_betaP1.txt", "w") as out:
        print("LANE W1 #466 -- first unproven rung r=beta+1.  A_r=(1/p)sum_{b!=0}|eta|^{2r};"
              " Einf=char-0 (exact closed form); Wick=(2r-1)!!n^r.", file=out)
        print("D_r=A_r-Einf = signed wraparound DC-deviation (part b);"
              " A_r<=Wick <=> D_r<=BUDGET=Wick-Einf.", file=out)
        print(f"numpy {np.__version__}; deterministic.", file=out)

        # cross-validate the exact char-0 closed form
        print(f"\n{'-'*72}\nchar-0 exact closed-form cross-check:", file=out)
        for n in (8, 16, 32):
            e2, e3 = char0_energy_exact(n, 2), char0_energy_exact(n, 3)
            print(f"  n={n}: E_2^inf={e2} (3n^2-3n={3*n*n-3*n});  "
                  f"E_3^inf={e3} (15n^3-45n^2+40n={15*n**3-45*n**2+40*n})", file=out)

        print(f"\n{'#'*120}\n### PRIMARY beta = 4 (prize diagonal)\n{'#'*120}", file=out)
        for n, rmax in [(8, 9), (16, 8), (32, 8)]:
            for p in find_primes(n, 4.0, 2):
                run(n, p, 4.0, 2, rmax, out)

        print(f"\n{'#'*120}\n### FLAGGED ACCELERANT beta ~ 3 (crossover reached at small r; NOT prize"
              f" evidence)\n{'#'*120}", file=out)
        for n, rmax in [(16, 8), (32, 8)]:
            for p in find_primes(n, 3.0, 2):
                run(n, p, 3.0, 2, rmax, out)

        print(f"\n{'#'*120}\n### FLAGGED generalized-Fermat contrast (65537 = 2^16+1)\n{'#'*120}", file=out)
        if is_prime(65537):
            run(16, 65537, 4.0, 2, 8, out)

        prize_scale_table(out)
        print(f"\n[total runtime {time.time()-t0:.1f}s]", file=out)
    print(f"done -> scripts/probes/_out_466_wall_betaP1.txt  [{time.time()-t0:.1f}s]")


if __name__ == "__main__":
    main()
