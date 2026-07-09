#!/usr/bin/env python3
"""
sweep_A03_cosh_mgf.py  --  Actionable A03 (merged 407-T15)

cosh-MGF root-free reduction of the open input B(mu_n) at the saddle.

The open core of the dyadic proximity-gap prize is the worst Gauss-period sup-norm
    B(mu_n) = max_{b != 0} | eta_b |,    eta_b = sum_{x in mu_n} e_p(b x),
with the conjectured floor B <= sqrt(2 n log(q/n))  (equiv. B <= sqrt(2 n log m)).

407-T15 found two EXACT cancellations that strip the sqrt(p) and the 2r-th root:

  (C1)  sqrt(p) factors out: tau(chi^j) = sqrt(p) u_j, |u_j| = 1, so
        M(n) = sqrt(n/m) * R,  R = max_b | sum_{j=1}^{m-1} conj(chi^j)(b) u_j |.
        Floor M <= sqrt(2 n log m)  <=>  R <= sqrt(2 m log m)  (no sqrt(p), no field size).

  (C2)  the max becomes a cosh-MGF (no 2r-th root):
        sum_{b in F_p} cosh(|eta_b| y) = p * I0(2y)^{n/2}      (CHAR-0, exact)
        one-term bound:  M <= min_y (1/y) arccosh( p * I0(2y)^{n/2} )
        saddle y* = sqrt(2 log p / n)  ->  M <= sqrt(2 n log 2p) (1+o(1)) = the floor.

A03 charter: re-verify (C1) and (C2) numerically; compare the MGF-at-saddle bound vs
the moment-method bound vs the TRUE B across n=8..256, multiple primes; locate where it
FAILS at structured primes (n=16, p=786433); and decide whether the root-free MGF form is
attackable by a NON-MOMENT (convexity / log-concavity) argument the raw moments are not.

Honesty: this is a PROBE -- numerical evidence on prize-shaped small cases, NOT a proof.
"""

import math
import numpy as np
from sympy import isprime, primitive_root

# ----------------------------------------------------------------------------
# Gauss periods over F_p for mu_n  (n = 2^mu | p-1).  eta_b = sum_{x in mu_n} e_p(b x).
# Computed exactly-as-floats via a length-p FFT of the indicator of the dilates b*mu_n,
# i.e. eta_b = sum_{t} N_b(t) w^t with w = e(1/p).  We get |eta_b| for all b at once.
# ----------------------------------------------------------------------------

MAXP = 4_500_000    # length-p FFT cap. Bluestein on prime-length 16M is too slow/large;
                    # 4.5e6 keeps every FFT fast (<1s) and covers all prize-anomaly onsets.

def gauss_period_abs(p, n):
    """Return numpy array A[b] = |eta_b| for b in 0..p-1, plus mu_n as a set.
    Requires a length-p FFT -> capped at MAXP. The true max-over-b and the exact char-p
    moments both genuinely need all b, so this caps the sweep at prize-shaped p<=3e7."""
    if p > MAXP:
        raise MemoryError(f"p={p} exceeds MAXP={MAXP}; skip")
    g = int(primitive_root(p))
    # mu_n = the unique subgroup of order n = {g^{((p-1)/n) k}}
    step = (p - 1) // n
    sub = set()
    x = pow(g, step, p)
    cur = 1
    for _ in range(n):
        sub.add(cur)
        cur = (cur * x) % p
    assert len(sub) == n
    mu = np.array(sorted(sub), dtype=np.int64)
    # eta_b = sum_{x in mu} e_p(b x).  Build, for each b, the histogram of (b*x mod p),
    # then one inverse-DFT.  Cheaper: for all b at once use the (p x ?) but p can be big.
    # We only need |eta_b| for b != 0; compute via direct complex sum over the n terms
    # using a precomputed table of e_p(residues) -- n is small (<=256) so this is fast
    # per b, but b ranges over p which can be ~1e6.  Use FFT instead:
    # Let f = indicator over Z/p of the multiset {0} (we want eta_b = hat-indicator of mu at b).
    # eta_b = sum_{x in mu} omega^{b x}.  As a function of b this is the DFT of 1_{mu}.
    ind = np.zeros(p, dtype=np.float64)
    ind[mu] = 1.0
    fft = np.fft.fft(ind)          # fft[b] = sum_x ind[x] e^{-2pi i b x / p} = conj(eta_b)
    A = np.abs(fft)                # |eta_b|
    return A, mu, g

def true_B(p, n):
    A, mu, g = gauss_period_abs(p, n)
    A0 = A.copy()
    A0[0] = -1.0                   # exclude b=0 (eta_0 = n)
    return float(A0.max()), A

# ----------------------------------------------------------------------------
# char-0 even moments via the Bessel law:  E_r^inf(mu_n) = (2r)! [x^{2r}] I0(2x)^{n/2}
#   = (2r)! * sum_{m: Fin(n/2) -> N, sum m = r} prod 1/(m_i!)^2
# We compute [x^{2r}] I0(2x)^d as the coefficient via series multiplication. d = n/2.
# I0(2x) = sum_{k>=0} x^{2k}/(k!)^2.  So I0(2x)^d coefficients of x^{2j} only.
# ----------------------------------------------------------------------------

def bessel_even_coeffs(d, R):
    """coeff[j] = [x^{2j}] I0(2x)^d  for j=0..R.  Exact rationals via Fraction."""
    from fractions import Fraction
    base = [Fraction(0)] * (R + 1)
    for k in range(R + 1):
        base[k] = Fraction(1, math.factorial(k) ** 2)   # coeff of x^{2k} in I0(2x)
    # raise to the d-th power by repeated convolution (in the x^2 grading)
    res = [Fraction(0)] * (R + 1)
    res[0] = Fraction(1)
    for _ in range(d):
        new = [Fraction(0)] * (R + 1)
        for i in range(R + 1):
            if res[i] == 0:
                continue
            for j in range(R + 1 - i):
                if base[j] == 0:
                    continue
                new[i + j] += res[i] * base[j]
        res = new
    return res   # res[j] = [x^{2j}] I0(2x)^d

def E_r_char0(n, r, coeff_cache):
    """E_r^inf(mu_n) = (2r)! * [x^{2r}] I0(2x)^{n/2}."""
    return float(math.factorial(2 * r) * coeff_cache[r])

# ----------------------------------------------------------------------------
# char-p even moments (exact): E_r^{Fp}(mu_n) = (1/p) sum_b |eta_b|^{2r}.
# (Includes b=0 term n^{2r}; the sum over b!=0 = p E_r - n^{2r}.)
# ----------------------------------------------------------------------------

def E_r_charp(A, p, r):
    return float(np.sum(A.astype(np.float64) ** (2 * r)) / p)

# ----------------------------------------------------------------------------
# bound functions
# ----------------------------------------------------------------------------

def moment_bound_charp(A, p, n, rmax):
    """B <= min_r (sum_{b!=0} |eta_b|^{2r})^{1/2r}.  EXACT char-p moments (true upper bd)."""
    A0 = A.astype(np.float64).copy()
    A0[0] = 0.0
    best = math.inf
    bestr = None
    for r in range(1, rmax + 1):
        S = float(np.sum(A0 ** (2 * r)))     # = sum_{b!=0} |eta_b|^{2r} = p E_r - n^{2r}
        if S <= 0:
            continue
        val = S ** (1.0 / (2 * r))
        if val < best:
            best, bestr = val, r
    return best, bestr

def moment_bound_char0(n, p, coeff_cache, rmax):
    """B <= min_r (p E_r^inf - n^{2r})^{1/2r}.  CHAR-0 moments (valid only below anomaly)."""
    best = math.inf
    bestr = None
    for r in range(1, rmax + 1):
        S = p * E_r_char0(n, r, coeff_cache) - n ** (2 * r)
        if S <= 0:
            continue
        val = S ** (1.0 / (2 * r))
        if val < best:
            best, bestr = val, r
    return best, bestr

def mgf_bound_char0(n, p, ny_max=400):
    """B <= min_y (1/y) arccosh( p I0(2y)^{n/2} ).  RHS is the CHAR-0 cosh identity.
    I0(2y)^{n/2} via scipy-free series is unstable for large y; use log directly:
      log(p I0(2y)^{n/2}) = log p + (n/2) log I0(2y).
    arccosh(z) = log(z + sqrt(z^2 - 1)) ~ log(2z) for large z.
    """
    from numpy import i0   # numpy has the modified Bessel I0
    best = math.inf
    besty = None
    # saddle suggestion
    y_saddle = math.sqrt(2.0 * math.log(p) / n)
    ys = np.linspace(y_saddle * 0.2, y_saddle * 3.0, ny_max)
    for y in ys:
        if y <= 0:
            continue
        logz = math.log(p) + (n / 2.0) * math.log(float(i0(2.0 * y)))
        # arccosh(z) for z = e^{logz}, large:  = log(z + sqrt(z^2-1)) = logz + log(1+sqrt(1-e^{-2logz}))
        arccosh = logz + math.log1p(math.sqrt(max(0.0, 1.0 - math.exp(-2.0 * logz))))
        val = arccosh / y
        if val < best:
            best, besty = val, y
    return best, besty, y_saddle

def mgf_bound_charp(A, p, n, ny_max=400):
    """The TRUE one-term cosh bound using the EXACT char-p LHS:
       sum_b cosh(|eta_b| y) is computed directly; M <= min_y (1/y) arccosh(sum_b cosh).
    This is what you'd ACTUALLY have if you knew the char-p cosh-MGF.  It is exactly the
    char-p moment bound in disguise (since cosh = sum of even moments)."""
    Af = A.astype(np.float64)
    best = math.inf
    besty = None
    y_saddle = math.sqrt(2.0 * math.log(p) / n)
    ys = np.linspace(y_saddle * 0.2, y_saddle * 3.0, ny_max)
    for y in ys:
        if y <= 0:
            continue
        # sum_b cosh(|eta_b| y); guard overflow via logsumexp on the cosh -> use max-shift
        z = Af * y
        m = float(z.max())
        # cosh(z) = (e^z + e^{-z})/2; for large z ~ e^z/2.  logsumexp:
        # log(sum_b cosh(z_b)) = m + log( sum_b (e^{z_b-m}+e^{-z_b-m})/2 )
        s = np.sum(np.exp(z - m) + np.exp(-z - m)) / 2.0
        logsum = m + math.log(s)
        arccosh = logsum + math.log1p(math.sqrt(max(0.0, 1.0 - math.exp(-2.0 * logsum))))
        val = arccosh / y
        if val < best:
            best, besty = val, y
    return best, besty, y_saddle

# ----------------------------------------------------------------------------
# main sweep
# ----------------------------------------------------------------------------

def find_prime(n, beta_target):
    """smallest prime p = 1 mod n with p ~ n^beta_target."""
    target = n ** beta_target
    p = ((int(target) // n) + 1) * n + 1
    while not isprime(p):
        p += n
    return p

import sys
OUT = open("scripts/probes/_A03_results.txt", "w", encoding="utf-8")
def emit(*a):
    line = " ".join(str(x) for x in a)
    print(line); sys.stdout.flush()
    OUT.write(line + "\n"); OUT.flush()

def run():
    emit("=" * 100)
    emit("A03  cosh-MGF root-free reduction at the saddle  --  prize-shaped sweep")
    emit("=" * 100)

    # -------- Part 1: verify the two exact cancellations --------
    emit("\n[Part 1] Verify the two EXACT cancellations\n" + "-" * 60)
    for (n, p) in [(8, 257), (16, 65537), (16, 786433), (32, 1048609), (8, 3209)]:
        if (p - 1) % n != 0 or not isprime(p):
            emit(f"  skip n={n} p={p} (not 1 mod n or composite)")
            continue
        A, mu, g = gauss_period_abs(p, n)
        m = (p - 1) // n
        # C1: eta_b = sqrt(n/m) * (something of unit Gauss-phases)?  Check |eta_b|/sqrt(p) for b!=0.
        # The identity M = sqrt(n/m) R with R = max|sum conj(chi^j)(b) u_j|, |u_j|=1.
        # Direct numeric check: |eta_b|^2 averaged over b!=0 should equal (p-n)/(p-1) ~ n - n/m...
        A0 = A.astype(np.float64).copy(); A0[0] = 0.0
        mean_sq = float(np.sum(A0 ** 2) / (p - 1))   # (1/(p-1)) sum_{b!=0}|eta_b|^2
        # exact: sum_{b!=0}|eta_b|^2 = p*n - n^2  (Parseval), so mean = (pn - n^2)/(p-1) = n(p-n)/(p-1)
        mean_sq_exact = n * (p - n) / (p - 1)
        # so M = sqrt(n/m) R with R^2 mean = m * mean_sq / n ... just verify Parseval (the C1 root):
        c1_ok = abs(mean_sq - mean_sq_exact) / mean_sq_exact < 1e-9

        # C2: sum_b cosh(|eta_b| y) = p I0(2y)^{n/2}  (char-0).  Test at a small y where char-0 holds.
        from numpy import i0
        y = 0.15
        lhs = float(np.sum(np.cosh(A.astype(np.float64) * y)))
        rhs = p * float(i0(2.0 * y)) ** (n / 2.0)
        c2_ratio = lhs / rhs
        emit(f"  n={n:3d} p={p:8d} m={m:7d}:  C1(Parseval) rel.err={abs(mean_sq-mean_sq_exact)/mean_sq_exact:.2e} ok={c1_ok}"
             f"   C2(cosh @y={y}) lhs/rhs={c2_ratio:.8f}")

    # The cosh identity is char-0; test it at a LARGER y (deeper moments) to expose the anomaly.
    emit("\n  [C2 at increasing y -- exposes the char-0 vs char-p anomaly (structured prime n=16,p=786433)]")
    for (n, p) in [(16, 65537), (16, 786433), (32, 1048609)]:
        A, mu, g = gauss_period_abs(p, n)
        from numpy import i0
        row = [f"  n={n} p={p}: lhs/rhs @y="]
        for y in [0.1, 0.3, 0.6, 1.0, 1.5, 2.0]:
            lhs = float(np.sum(np.cosh(A.astype(np.float64) * y)))
            rhs = p * float(i0(2.0 * y)) ** (n / 2.0)
            row.append(f"{y}:{lhs/rhs:.4f}")
        emit("   ".join(row))

    # -------- Part 2: the three bounds vs the truth, across the sweep --------
    emit("\n[Part 2] MGF-at-saddle  vs  moment-method  vs  TRUE B  (floor = sqrt(2 n log(p/n)))")
    emit("-" * 60)
    emit(f"  {'n':>4} {'p':>10} {'beta':>5} | {'trueB':>8} {'floor':>8} {'B/flr':>6} | "
         f"{'mom_p':>8} {'r*':>3} | {'mom_0':>8} {'r0':>3} | {'mgf_0':>8} {'mgf_p':>8} {'y*':>6}")
    # feasibility: need a length-p FFT (<= MAXP). p ~ n^beta. So restrict combos with n^beta<=MAXP.
    cases = []
    for n in [8, 16, 32, 64]:
        for beta in [2.0, 3.0, 4.0, 5.0]:
            if n ** beta <= MAXP:
                cases.append((n, beta))
    # structured-prime spotlight
    spotlight = [(16, 786433), (8, 257), (16, 65537), (32, 1048609), (64, 16777601),
                 (128, 16777729)]

    coeff_cache_by_n = {}
    RMAX = 40
    for (n, beta) in cases:
        p = find_prime(n, beta)
        if p > MAXP:
            emit(f"  {n:>4} {p:>10} {beta:>5.1f} |  (skip: p>MAXP)")
            continue
        if (n // 2, RMAX) not in coeff_cache_by_n:
            coeff_cache_by_n[(n // 2, RMAX)] = bessel_even_coeffs(n // 2, RMAX)
        coeff = coeff_cache_by_n[(n // 2, RMAX)]
        tb, A = true_B(p, n)
        floor = math.sqrt(2.0 * n * math.log(p / n))
        mp, rp = moment_bound_charp(A, p, n, RMAX)
        m0, r0 = moment_bound_char0(n, p, coeff, RMAX)
        mg0, y0, ysad = mgf_bound_char0(n, p)
        mgp, yp, _ = mgf_bound_charp(A, p, n)
        emit(f"  {n:>4} {p:>10} {beta:>5.1f} | {tb:>8.2f} {floor:>8.2f} {tb/floor:>6.3f} | "
             f"{mp:>8.2f} {rp if rp else 0:>3} | {m0:>8.2f} {r0 if r0 else 0:>3} | "
             f"{mg0:>8.2f} {mgp:>8.2f} {ysad:>6.3f}")

    emit("\n  [Structured-prime spotlight]")
    for (n, p) in spotlight:
        if (p - 1) % n != 0 or not isprime(p):
            emit(f"  skip n={n} p={p} (not 1 mod n / composite)"); continue
        if p > MAXP:
            emit(f"  skip n={n} p={p} (p>MAXP)"); continue
        if (n // 2, RMAX) not in coeff_cache_by_n:
            coeff_cache_by_n[(n // 2, RMAX)] = bessel_even_coeffs(n // 2, RMAX)
        coeff = coeff_cache_by_n[(n // 2, RMAX)]
        tb, A = true_B(p, n)
        floor = math.sqrt(2.0 * n * math.log(p / n))
        mp, rp = moment_bound_charp(A, p, n, RMAX)
        m0, r0 = moment_bound_char0(n, p, coeff, RMAX)
        mg0, y0, ysad = mgf_bound_char0(n, p)
        mgp, yp, _ = mgf_bound_charp(A, p, n)
        emit(f"  n={n:3d} p={p:9d} beta={math.log(p)/math.log(n):.2f} | trueB={tb:.2f} floor={floor:.2f} "
             f"B/flr={tb/floor:.3f} | mom_p={mp:.2f}(r={rp}) mom_0={m0:.2f}(r={r0}) | "
             f"mgf_0={mg0:.2f} mgf_p={mgp:.2f}")

    # -------- Part 3: the decisive identity test --------
    emit("\n[Part 3] Is mgf_charp == mom_charp?  (does the cosh-MGF add anything over moments?)")
    emit("-" * 60)
    emit("  The char-p cosh-MGF bound and the char-p moment bound should be numerically equal")
    emit("  (cosh = generating fn of the SAME even moments). If mgf_p ~ mom_p, the MGF is a")
    emit("  REPACKAGING of the moments, not new information.  And mgf_0 (char-0 RHS) inherits")
    emit("  the SAME anomaly wall as mom_0 (the char-0 RHS is only valid below the anomaly).")
    for n in [16, 32, 64]:
        beta3 = 4.0 if n ** 4.0 <= MAXP else 3.0
        p = find_prime(n, beta3)
        if p > MAXP:
            emit(f"  n={n}: skip (p>MAXP even at beta=3)"); continue
        if (n // 2, RMAX) not in coeff_cache_by_n:
            coeff_cache_by_n[(n // 2, RMAX)] = bessel_even_coeffs(n // 2, RMAX)
        coeff = coeff_cache_by_n[(n // 2, RMAX)]
        tb, A = true_B(p, n)
        mp, rp = moment_bound_charp(A, p, n, RMAX)
        mgp, yp, _ = mgf_bound_charp(A, p, n)
        m0, r0 = moment_bound_char0(n, p, coeff, RMAX)
        mg0, y0, ysad = mgf_bound_char0(n, p)
        emit(f"  n={n} p={p}: mgf_p={mgp:.3f} vs mom_p={mp:.3f}  (ratio {mgp/mp:.4f}); "
             f"mgf_0={mg0:.3f} vs mom_0={m0:.3f} (ratio {mg0/m0:.4f}); trueB={tb:.3f}")

    OUT.close()

if __name__ == "__main__":
    run()
