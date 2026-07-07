#!/usr/bin/env python3
"""
probe_466_jacobi_ramp_defect.py -- Lane R4 (#466): the ensemble ramp-defect law for the
Jacobi recurrence of the empirical spectral measure of {eta_b : b != 0}.

Round-1 P4 (probe_466_hankel_turnover.py) measured 1 - q_1 = (n-1)/(p-1) + n/(p-1)^2
exact to ~1e-13.  This probe DERIVES that law and the j=2 analogue exactly, then
validates against the actual spectrum.

SETUP.  eta_b = sum_{x in mu_n} e_p(bx), b != 0; n even so -1 in mu_n and eta_b is REAL.
mu_emp = uniform measure on {eta_b : b != 0} (= uniform on the m = (p-1)/n Gauss-period
values).  Raw moments M_k = (1/(p-1)) sum_{b!=0} eta_b^k are EXACT rationals:
    sum_{all b} eta_b   = 0            => M_1 = -n/(p-1)
    sum_{all b} eta_b^2 = p*E_1 = p*n  => M_2 = n(p-n)/(p-1)          (Parseval)
    sum_{all b} eta_b^3 = p*T_3        => M_3 = (p*T_3 - n^3)/(p-1)
    sum_{all b} eta_b^4 = p*E_2        => M_4 = (p*E_2 - n^4)/(p-1)
with E_r the additive 2r-energy of mu_n and T_3 = #{(x,y,z) in mu_n^3 : x+y+z = 0}.
CLEAN regime (generic prime): E_2 = 3n^2 - 3n (even n) and T_3 = 0.

JACOBI.  The measure is NOT centered (mean M_1 = -n/(p-1)) and NOT exactly even
(skewness c_3 = O(n^3/p) != 0).  The true three-term-recurrence coefficients are
    a_0 = M_1,  b_1^2 = c_2,  a_1 = M_1 + c_3/c_2,  b_2^2 = c_4/c_2 - (c_3/c_2)^2 - c_2
with c_k the CENTRAL moments.  The probe distinguishes three j=2 prescriptions:
    FULL      : b_2^2 = c_4/c_2 - (c_3/c_2)^2 - c_2   (the actual spectrum's law)
    CEN-EVEN  : b_2^2 = c_4/c_2 - c_2                  (drop skewness)
    RAW-EVEN  : b_2^2 = M_4/M_2 - M_2                  (lane brief's shorthand)

DERIVED CLOSED FORMS (clean regime; verified symbolically below and numerically):
  j=1:  b_1^2 = n*p*(p-1-n)/(p-1)^2
        1 - b_1^2/n           = (n-1)/(p-1) + n/(p-1)^2   [round-1's measured law]
        1 - M_2/n             = (n-1)/(p-1)               [raw Parseval variant]
  j=2:  b_2^2 = (p-1)*((2n-3)*p - (n^3-3)) / (p-1-n)^2    [FULL]
        1 - b_2^2/(2n)   = (3(p-1)^2 - 4n^2(p-1) - 2n(p-1) + n^3(p+1)) / (2n(p-1-n)^2)
                         -> 3/(2n) + (n^2/2 - 2n + 2)/(p-1) + O(1/(p-1)^2)
        1 - b_2^2/(2n-3) = (n(n-2)^2(p-1) + n^2(2n-3)) / ((2n-3)(p-1-n)^2)
                         -> n(n-2)^2/((2n-3)(p-1))        [char-0-normalized pure ramp]
  (char-0 reference b_2^{(0)2} = 2n-3, matching round-1's self-test b_2^2 = (2-3/n)n.)

VALIDATION per instance: (i) exact integer E_2, T_3 (clean/anomalous flag); (ii) exact
rational Jacobi from the energies vs the closed forms (Fraction equality, deviation must
be EXACTLY 0 on clean instances); (iii) float64 Lanczos on the actual Gauss-period
spectrum vs the closed forms (max relative deviation reported = part (b) deliverable).

Regime discipline: p = 1 mod n, p >= n^4 (beta >= 4), mu_n PROPER (never n = p-1),
>= 3 primes per n in {8, 16, 32}; Fermat 65537 at n=16 included as a flagged
structured extra.

HONESTY: this pins the ENSEMBLE MEAN ramp only (the j=1,2 laws read (n,p) and the clean
energies -- round-1 showed the window reads p, not the instance); the worst-case
turnover k*(instance) and everything at depth j >= 3 stay OPEN.
"""

import math
import time
from fractions import Fraction

import numpy as np


# ---------------------------------------------------------------- number theory
def is_prime(x: int) -> bool:
    if x < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
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


def next_prime_1mod(n: int, start: int, exclude=()) -> int:
    p = start
    r = p % n
    if r != 1:
        p += (1 - r) % n
    while True:
        if p not in exclude and is_prime(p):
            return p
        p += n


def factorize(x: int):
    fs, d = {}, 2
    while d * d <= x:
        while x % d == 0:
            fs[d] = fs.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        fs[x] = fs.get(x, 0) + 1
    return fs


def primitive_root(p: int) -> int:
    qs = list(factorize(p - 1))
    g = 2
    while True:
        if all(pow(g, (p - 1) // q, p) != 1 for q in qs):
            return g
        g += 1


# ---------------------------------------------------------------- symbolic derivation
def symbolic_derivation():
    import sympy as sp

    n, p = sp.symbols('n p', positive=True)
    P = p - 1
    M1, M2, M3, M4 = -n / P, n * (p - n) / P, -n**3 / P, (p * (3 * n**2 - 3 * n) - n**4) / P
    c2 = sp.simplify(M2 - M1**2)
    c3 = sp.simplify(M3 - 3 * M1 * M2 + 2 * M1**3)
    c4 = sp.simplify(M4 - 4 * M1 * M3 + 6 * M1**2 * M2 - 3 * M1**4)
    b1sq = c2
    b2sq_full = sp.simplify(c4 / c2 - (c3 / c2)**2 - c2)
    checks = {
        "b1^2 = n*p*(p-1-n)/(p-1)^2":
            sp.simplify(b1sq - n * p * (p - 1 - n) / (p - 1)**2),
        "1 - b1^2/n = (n-1)/(p-1) + n/(p-1)^2":
            sp.simplify(1 - b1sq / n - ((n - 1) / P + n / P**2)),
        "1 - M2/n = (n-1)/(p-1)":
            sp.simplify(1 - M2 / n - (n - 1) / P),
        "b2^2(FULL) = (p-1)((2n-3)p - (n^3-3))/(p-1-n)^2":
            sp.simplify(b2sq_full - (p - 1) * ((2 * n - 3) * p - (n**3 - 3)) / (p - 1 - n)**2),
        "1 - b2^2/(2n) = (3(p-1)^2-4n^2(p-1)-2n(p-1)+n^3(p+1))/(2n(p-1-n)^2)":
            sp.simplify(1 - b2sq_full / (2 * n)
                        - (3 * P**2 - 4 * n**2 * P - 2 * n * P + n**3 * (p + 1))
                        / (2 * n * (p - 1 - n)**2)),
        "1 - b2^2/(2n-3) = (n(n-2)^2(p-1)+n^2(2n-3))/((2n-3)(p-1-n)^2)":
            sp.simplify(1 - b2sq_full / (2 * n - 3)
                        - (n * (n - 2)**2 * P + n**2 * (2 * n - 3))
                        / ((2 * n - 3) * (p - 1 - n)**2)),
    }
    print("== SYMBOLIC DERIVATION (sympy; every residual must be 0) ==")
    for k, v in checks.items():
        print(f"  [{'OK' if v == 0 else 'FAIL'}] {k}   residual = {v}")
    assert all(v == 0 for v in checks.values())
    print()


# ---------------------------------------------------------------- exact energies
def exact_energies(n: int, p: int):
    """(E_2, T_3) exactly, from the n^2 pairwise sums of mu_n."""
    g = primitive_root(p)
    m = (p - 1) // n
    h = pow(g, m, p)  # generator of mu_n
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = x * h % p
    mu_set = set(mu)
    r = {}
    for a in mu:
        for b in mu:
            c = (a + b) % p
            r[c] = r.get(c, 0) + 1
    E2 = sum(v * v for v in r.values())
    T3 = sum(v for c, v in r.items() if (p - c) % p in mu_set)
    return E2, T3


# ---------------------------------------------------------------- exact rational Jacobi
def exact_jacobi(n: int, p: int, E2: int, T3: int):
    """Exact rational (b1^2, b2^2_full, b2^2_ceneven, b2^2_raweven, c3) from energies."""
    P = p - 1
    M1 = Fraction(-n, P)
    M2 = Fraction(n * (p - n), P)
    M3 = Fraction(p * T3 - n**3, P)
    M4 = Fraction(p * E2 - n**4, P)
    c2 = M2 - M1**2
    c3 = M3 - 3 * M1 * M2 + 2 * M1**3
    c4 = M4 - 4 * M1 * M3 + 6 * M1**2 * M2 - 3 * M1**4
    b1sq = c2
    b2sq_full = c4 / c2 - (c3 / c2)**2 - c2
    b2sq_cen = c4 / c2 - c2
    b2sq_raw = M4 / M2 - M2
    return b1sq, b2sq_full, b2sq_cen, b2sq_raw, c3


# ---------------------------------------------------------------- closed forms
def closed_forms(n: int, p: int):
    P = p - 1
    b1sq = Fraction(n * p * (P - n), P**2)
    b2sq = Fraction((P) * ((2 * n - 3) * p - (n**3 - 3)), (P - n)**2)
    return b1sq, b2sq


# ---------------------------------------------------------------- float spectrum
def gauss_period_spectrum(n: int, p: int):
    g = primitive_root(p)
    L = p - 1
    m = L // n
    R = np.empty(L, dtype=np.uint64)
    R[0] = 1
    filled = 1
    while filled < L:
        step = min(filled, L - filled)
        gl = pow(g, filled, p)
        R[filled:filled + step] = (R[:step] * np.uint64(gl)) % np.uint64(p)
        filled += step
    eta = np.zeros(m)
    w = 2.0 * np.pi / p
    for j in range(n):
        eta += np.cos(w * R[j * m:(j + 1) * m].astype(np.float64))
    del R
    return eta


def lanczos(x: np.ndarray, K: int, passes: int = 2):
    msz = x.size
    K = min(K, msz - 1)
    V = np.empty((msz, K + 1))
    V[:, 0] = 1.0 / math.sqrt(msz)
    a = np.zeros(K)
    b = np.zeros(K)
    for k in range(K):
        u = x * V[:, k]
        a[k] = float(V[:, k] @ u)
        u = u - a[k] * V[:, k]
        if k > 0:
            u -= b[k - 1] * V[:, k - 1]
        for _ in range(passes):
            c = V[:, :k + 1].T @ u
            u -= V[:, :k + 1] @ c
        nb = float(np.linalg.norm(u))
        b[k] = nb
        V[:, k + 1] = u / nb
    return a, b


# ---------------------------------------------------------------- main
def main():
    symbolic_derivation()

    instances = []
    for n in (8, 16, 32):
        start = n**4 + 1
        got, p = [], None
        while len(got) < 3:
            p = next_prime_1mod(n, start if p is None else p + n, exclude=got)
            got.append(p)
        for i, p in enumerate(got):
            instances.append((n, p, f"gen{i + 1}"))
    instances.append((16, 65537, "FERMAT"))
    instances.sort()

    print("== INSTANCES (>=3 generic primes per n, beta >= 4, mu_n proper) ==")
    hdr = (f"  {'n':>3} {'p':>9} {'tag':>7} {'beta':>6} {'E2':>7} {'T3':>4} {'clean':>5}"
           f" {'exact=CF':>8} {'relDev b1^2':>12} {'relDev b2^2':>12}"
           f" {'relDev 1-q1':>12} {'relDev 1-q2':>12} {'relDev(cen-even)':>16} {'relDev(raw-even)':>16}")
    print(hdr)

    max_dev = {"b1sq": 0.0, "b2sq": 0.0, "q1": 0.0, "q2": 0.0}
    for n, p, tag in instances:
        t0 = time.time()
        beta = math.log(p, n)
        E2, T3 = exact_energies(n, p)
        clean = (E2 == 3 * n * n - 3 * n) and (T3 == 0)

        b1_ex, b2_ex, b2_cen, b2_raw, c3 = exact_jacobi(n, p, E2, T3)
        b1_cf, b2_cf = closed_forms(n, p)
        exact_eq = (b1_ex == b1_cf) and (b2_ex == b2_cf)  # must hold iff clean

        eta = gauss_period_spectrum(n, p)
        _, b = lanczos(eta, 3)
        b1sq_f, b2sq_f = b[0]**2, b[1]**2

        d_b1 = abs(b1sq_f - float(b1_cf)) / float(b1_cf)
        d_b2 = abs(b2sq_f - float(b2_cf)) / float(b2_cf)
        # ramp defects (the law targets): compare measured 1-q vs closed-form 1-q
        q1_cf = float(Fraction((n - 1) * (p - 1) + n, (p - 1)**2))
        q1_ms = 1.0 - b1sq_f / n
        d_q1 = abs(q1_ms - q1_cf) / q1_cf
        q2_cf = float(Fraction(3 * (p - 1)**2 - 4 * n**2 * (p - 1) - 2 * n * (p - 1)
                               + n**3 * (p + 1), 2 * n * (p - 1 - n)**2))
        q2_ms = 1.0 - b2sq_f / (2 * n)
        d_q2 = abs(q2_ms - q2_cf) / q2_cf
        # how far the even prescriptions sit from the ACTUAL spectrum (not the law):
        d_cen = abs(float(b2_cen) - b2sq_f) / b2sq_f
        d_raw = abs(float(b2_raw) - b2sq_f) / b2sq_f

        if clean:
            max_dev["b1sq"] = max(max_dev["b1sq"], d_b1)
            max_dev["b2sq"] = max(max_dev["b2sq"], d_b2)
            max_dev["q1"] = max(max_dev["q1"], d_q1)
            max_dev["q2"] = max(max_dev["q2"], d_q2)

        print(f"  {n:>3} {p:>9} {tag:>7} {beta:6.3f} {E2:>7} {T3:>4} {str(clean):>5}"
              f" {str(exact_eq):>8} {d_b1:12.2e} {d_b2:12.2e}"
              f" {d_q1:12.2e} {d_q2:12.2e} {d_cen:16.2e} {d_raw:16.2e}"
              f"   [{time.time() - t0:.1f}s]")
        if clean and not exact_eq:
            print("  *** FAIL: clean instance but exact rational Jacobi != closed form ***")
        if (not clean) and exact_eq:
            print("  *** NOTE: anomalous instance yet closed form holds (unexpected) ***")

    print("\n== SUMMARY (clean instances; float64 spectrum vs exact closed forms) ==")
    print(f"  max relative deviation  b_1^2 : {max_dev['b1sq']:.2e}")
    print(f"  max relative deviation  b_2^2 : {max_dev['b2sq']:.2e}")
    print(f"  max relative deviation 1-q_1  : {max_dev['q1']:.2e}   "
          f"(law: (n-1)/(p-1) + n/(p-1)^2)")
    print(f"  max relative deviation 1-q_2  : {max_dev['q2']:.2e}   "
          f"(law: (3(p-1)^2-4n^2(p-1)-2n(p-1)+n^3(p+1))/(2n(p-1-n)^2))")
    print("\n  NOTE: 'exact=CF' compares the EXACT rational Jacobi (from integer E_2, T_3)")
    print("  with the closed forms -- True means the deviation is EXACTLY 0 as rationals.")
    print("  The cen-even/raw-even columns show those prescriptions deviate from the actual")
    print("  spectrum at O(n^2(n-3)^2/p^2) / O(n/p) respectively: the FULL (skewness-aware)")
    print("  law is the one the spectrum obeys to float precision.")
    print("\n  HONESTY: ensemble-MEAN ramp law only (j=1,2). Worst-case turnover k*(instance)")
    print("  and depth j>=3 remain OPEN; the window reads p, not the instance (round-1 P4).")


if __name__ == "__main__":
    main()
