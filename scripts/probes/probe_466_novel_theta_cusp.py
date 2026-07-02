#!/usr/bin/env python3
"""
probe_466_novel_theta_cusp.py -- lane N1-theta-cusp (#466, round "novel", 2026-07-01)

The theta-cusp chain: theta(L_p) for the WRAPAROUND lattice
    L_p = ker(Z^n -> F_p, e_j -> h^j),   h of exact order n = 2^mu, p = 1 (mod n)
is a modular form of weight n/2 on Gamma_0(4p^2); decompose Eisenstein + cusp;
Eisenstein = Siegel genus average; cusp <= Deligne.  This probe pins the two
load-bearing constants of the chain at exact small scales and extrapolates the
ledger to the prize point:

  (1) ANCHOR (unconditional): r_{L_p}(2) = n exactly (kissing number), for every
      p = 1 mod n.  Verified exactly here.
  (2) EISENSTEIN =/= WICK: the Siegel/genus main term at index m is the VOLUME
      term  pi^{n/2} m^{n/2-1} S(m) / (Gamma(n/2) p),  which at prize indices
      m = 2r ~ 178 << n is doubly-exponentially negligible, while the true count
      is the Wick term r_{L_0}(m) (the antipodal-pair sublattice L_0 = sqrt2 Z^{n/2}).
      The anomaly ratio r(m)/a_E(m) is measured to explode with n.
  (3) WICK+DC MODEL: r_pred(m) = r_{L_0}(m) + (r_{Z^n}(m) - r_{L_0}(m))/p tracks
      the exact r_{L_p}(m) (this is the D2 / Rogers-Siegel random-sublattice shape).
  (4) DEATH LEDGER: the best per-form transfer the cusp side can ever give is
        |a_S(m)| <= a_S(anchor) * d(m) * (m/m_anchor)^{(k-1)/2},   k = n/2,
      and (m/2)^{(k-1)/2} at the prize is 10^{5.2e8} -- worse than the TRIVIAL
      count 10^{1339} by half a billion orders of magnitude.  The crossover where
      the modular ceiling stops beating the trivial count is n* ~ 2^8 (the same
      effective range as the #407 exact-norm height gate -- it is the SAME
      exponential (2r)^{n/4} in automorphic clothing).

Method: exact residue-resolved DP over Z^n coordinates (int64, all counts < 2^53),
cross-checked at n=8 by brute-force enumeration and at every n by the polynomial
identity sum_rho DP[m][rho] = r_{Z^n}(m).
"""

import numpy as np
from math import lgamma, log, log10, pi, comb

LOG10E = log10(np.e)


# ---------- tiny number theory ----------

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


def find_h(n: int, p: int) -> int:
    """element of exact order n = 2^mu in F_p^* (h^{n/2} = -1 certifies exact order)."""
    assert (p - 1) % n == 0
    e = (p - 1) // n
    for g in range(2, p):
        h = pow(g, e, p)
        if pow(h, n // 2, p) == p - 1:
            return h
    raise RuntimeError("no element of exact order found")


def divisor_count(m: int) -> int:
    c, x, d = 1, m, 2
    while d * d <= x:
        if x % d == 0:
            e = 0
            while x % d == 0:
                x //= d
                e += 1
            c *= e + 1
        d += 1
    if x > 1:
        c *= 2
    return c


# ---------- exact representation numbers ----------

def theta_coeffs_Zn(n: int, mmax: int):
    """r_{Z^n}(m) for m <= mmax, exact ints, via 1-D theta power."""
    amax = int(mmax ** 0.5)
    base = [0] * (mmax + 1)
    base[0] = 1
    for a in range(1, amax + 1):
        if a * a <= mmax:
            base[a * a] += 2
    cur = [0] * (mmax + 1)
    cur[0] = 1
    for _ in range(n):
        new = [0] * (mmax + 1)
        for w1 in range(mmax + 1):
            if cur[w1] == 0:
                continue
            for w2 in range(mmax + 1 - w1):
                if base[w2]:
                    new[w1 + w2] += cur[w1] * base[w2]
        cur = new
    return cur


def rep_numbers_Lp(n: int, p: int, h: int, mmax: int):
    """Exact r_{L_p}(m), m <= mmax, by residue-resolved DP.  Also returns the
    DP row-sums (= r_{Z^n}(m)) as an internal consistency check."""
    amax = int(mmax ** 0.5)
    vals = [a for a in range(-amax, amax + 1)]
    W = [np.zeros(p, dtype=np.int64) for _ in range(mmax + 1)]
    W[0][0] = 1
    v = 1  # h^0
    for j in range(n):
        newW = [np.zeros(p, dtype=np.int64) for _ in range(mmax + 1)]
        for a in vals:
            a2 = a * a
            if a2 > mmax:
                continue
            shift = (a * v) % p
            for w in range(a2, mmax + 1):
                src = W[w - a2]
                if shift == 0:
                    newW[w] += src
                else:
                    newW[w] += np.roll(src, shift)
        W = newW
        v = (v * h) % p
    rL = [int(W[m][0]) for m in range(mmax + 1)]
    rZ_check = [int(W[m].sum()) for m in range(mmax + 1)]
    return rL, rZ_check


def brute_force_Lp(n: int, p: int, h: int, mmax: int):
    """independent enumeration over {-amax..amax}^n (n=8 only)."""
    amax = int(mmax ** 0.5)
    vals = np.arange(-amax, amax + 1, dtype=np.int64)
    res = np.zeros(1, dtype=np.int64)
    nrm = np.zeros(1, dtype=np.int64)
    v = 1
    for j in range(n):
        res = (res[:, None] + vals[None, :] * v) % p
        nrm = nrm[:, None] + vals[None, :] ** 2
        res, nrm = res.ravel(), nrm.ravel()
        keep = nrm <= mmax
        res, nrm = res[keep], nrm[keep]
        v = (v * h) % p
    out = [0] * (mmax + 1)
    hit = res == 0
    for m in range(mmax + 1):
        out[m] = int(np.count_nonzero(hit & (nrm == m)))
    return out


# ---------- analytic ledger ----------

def lchoose10(n: float, k: float) -> float:
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) * LOG10E


def eisenstein_log10(n: int, log10p: float, m: int) -> float:
    """log10 of the Siegel/genus main term pi^k m^{k-1} / (Gamma(k) p), k=n/2, S:=1."""
    k = n / 2
    return k * log10(pi) + (k - 1) * log10(m) - lgamma(k) * LOG10E - log10p


def ledger_row(n: int, log10p: float, r: int, label: str):
    k = n / 2.0
    m = 2 * r
    if m > n // 2:
        print(f"{label:>14} r={r:<4} m={m:<4} | [skipped: depth m > n/2, sparse regime "
              f"does not apply at this small n]")
        return
    triv = lchoose10(n, m) + m * log10(2)          # sparse {0,+-1} leading term of r_{Z^n}(m)
    dc = triv - log10p                              # DC / random-sublattice mean
    wick = lchoose10(n / 2, r) + r * log10(2)       # r_{L_0}(m) = r_{Z^{n/2}}(r) leading term
    dm = divisor_count(m)
    deligne = log10(n) + log10(dm) + ((k - 1) / 2) * log10(m / 2.0)
    aE = eisenstein_log10(n, log10p, m)
    dimS = log10((k - 1) / 12.0) + log10(6.0) + 2 * log10p
    step = ((k - 1) / 2) * log10(m / (m - 1.0))
    # largest anchor ratio m/m_a for which RP transfer stays below the DC target:
    rho_allow = 10 ** (max(dc, 0.0) * 2 / (k - 1)) if k > 1 else float("inf")
    print(f"{label:>14} r={r:<4} m={m:<4} | triv 10^{triv:12.1f} | DC 10^{dc:12.1f} | "
          f"Wick 10^{wick:9.1f} | Eis 10^{aE:15.1f} | Deligne-ceil 10^{deligne:13.1f} | "
          f"1-step 10^{step:10.1f} | dimS_k 10^{dimS:6.1f} | max-anchor-ratio {rho_allow:.6g}")


# ---------- main ----------

def run_instance(n: int, p: int, mmax: int, brute: bool):
    h = find_h(n, p)
    assert pow(h, n, p) == 1 and pow(h, n // 2, p) == p - 1
    print(f"\n=== n={n}, p={p} (p-1 = {(p-1)//n}*n), h={h}, h^(n/2) = -1 verified ===")
    rL, rZ_dp = rep_numbers_Lp(n, p, h, mmax)
    rZ = theta_coeffs_Zn(n, mmax)
    assert rZ_dp == rZ[: mmax + 1], "DP row-sum != independent r_{Z^n} -- DP bug"
    print("    [check] DP row-sums == polynomial r_{Z^n}(m): OK")
    if brute:
        bf = brute_force_Lp(n, p, h, mmax)
        assert bf == rL, f"brute force mismatch: {bf} vs {rL}"
        print("    [check] brute-force enumeration == DP: OK")
    # L_0 = sqrt2 Z^{n/2}: r_{L_0}(m) = r_{Z^{n/2}}(m/2) for even m
    rZhalf = theta_coeffs_Zn(n // 2, mmax // 2)
    rL0 = [rZhalf[m // 2] if m % 2 == 0 else 0 for m in range(mmax + 1)]
    # anchor
    print(f"    ANCHOR r(2) = {rL[2]}  (= n: {rL[2] == n})   [kissing number, unconditional]")
    onset = next((m for m in range(1, mmax + 1) if rL[m] != rL0[m]), None)
    print(f"    wraparound onset (first m with r != Wick): m = {onset}")
    print(f"    {'m':>3} {'r_Lp(m)':>14} {'Wick r_L0':>12} {'pred Wick+DC':>14} "
          f"{'r/pred':>8} {'Eis a_E (S=1)':>14} {'r/a_E':>10}")
    for m in range(2, mmax + 1):
        pred = rL0[m] + (rZ[m] - rL0[m]) / p
        aE = 10 ** eisenstein_log10(n, log10(p), m) if m > 0 else 0
        ratio = rL[m] / pred if pred > 0 else float("inf")
        ranom = rL[m] / aE if (aE > 0 and rL[m] > 0) else (0 if rL[m] == 0 else float("inf"))
        print(f"    {m:>3} {rL[m]:>14} {rL0[m]:>12} {pred:>14.2f} {ratio:>8.3f} "
              f"{aE:>14.4g} {ranom:>10.4g}")


def main():
    print("probe_466_novel_theta_cusp -- exact lattice data + the modular death ledger")

    # prize-diagonal small instances (p ~ n^4, p = 1 mod n)
    run_instance(8, 4129, 14, brute=True)
    run_instance(16, 65537, 16, brute=False)   # Fermat prize-diagonal
    run_instance(16, 65617, 16, brute=False)   # non-Fermat control
    # n=32 near 32^4 = 2^20
    p32 = 2 ** 20 + 1
    while not (p32 % 32 == 1 and is_prime(p32)):
        p32 += 32 if p32 % 32 == 1 else (1 - p32 % 32) % 32 + 1
    run_instance(32, p32, 14, brute=False)

    print("\n=== DEATH LEDGER: Deligne/Petersson transfer ceiling vs trivial count ===")
    print("   (Deligne-ceil = n*d(m)*(m/2)^{(k-1)/2}, the best any per-form bound anchored")
    print("    at the kissing number can give; 1-step = cost (m/(m-1))^{(k-1)/2} of moving")
    print("    ONE index; max-anchor-ratio = largest m/m_anchor for which the transfer")
    print("    stays below the DC target -- < 1 + 1/m means NO integer anchor exists.)")
    for n in (8, 16, 32, 128, 256, 512, 1024):
        log10p = 4 * log10(n)
        r = max(3, round(log(n ** 4)))
        ledger_row(n, log10p, r, f"n=2^{int(log(n)/log(2))}")
    for (n, log10p, r, tag) in (
        (2 ** 20, 4 * 20 * log10(2), 55, "n=2^20"),
        (2 ** 30, 120 * log10(2), 83, "n=2^30 b=4"),
        (2 ** 30, 120 * log10(2), 89, "n=2^30 r=89"),
        (2 ** 30, 158 * log10(2), 110, "n=2^30 q-lit"),
    ):
        ledger_row(n, log10p, r, tag)

    print("\nVERDICT: Eisenstein(prize index) ~ 10^{-3e9} (NOT the Wick term; the whole")
    print("count is cuspidal); Deligne/Petersson ceiling 10^{+5.2e8} vs trivial 10^{1339}")
    print("vs DC target 10^{1303}: the modular route is worse than trivial by 10^{5.2e8}.")
    print("The transfer cost (m/2)^{(k-1)/2} = (r)^{~n/4} IS the (2w)^{n/4} norm-height")
    print("wall in automorphic clothing; effective range n <~ 2^8 (matches #407 gate).")


if __name__ == "__main__":
    main()
