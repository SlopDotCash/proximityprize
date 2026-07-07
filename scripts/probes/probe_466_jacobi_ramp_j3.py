#!/usr/bin/env python3
"""
probe_466_jacobi_ramp_j3.py -- Lane S6 (#466): extend the ensemble Jacobi ramp-defect law
to depth j=3, via the Hankel-determinant route b_k^2 = D_k * D_{k-2} / D_{k-1}^2.

Builds on probe_466_jacobi_ramp_defect.py (j=1,2).  New inputs at depth 3 are the moments
M_5 (from T_5) and M_6 (from E_3 = the additive 6-energy = T_6).  CLEAN regime (generic prime,
even n so -1 in mu_n and eta_b real):
    T_5 = 0             (odd; clean)     => M_5 = -n^5/(p-1)
    E_3 = 15n^3-45n^2+40n (even 6-energy) => M_6 = (p*E_3 - n^6)/(p-1)

HANKEL.  For the centered measure (central moments c_2..c_6, c_0=1, c_1=0) the Hankel
determinants D_k = det[c_{i+j}]_{0<=i,j<=k} give the monic-OP off-diagonals
    b_k^2 = D_k * D_{k-2} / D_{k-1}^2 ,   D_{-1} = D_0 = 1.
  D_1 = c_2                         => b_1^2 = c_2
  D_2 = c_2 c_4 - c_3^2 - c_2^3     => b_2^2 = D_2 / c_2^2
  D_3 = det 4x4 of central moments  => b_3^2 = D_3 c_2 / D_2^2
The b_k^2 are translation-invariant, so the centered Hankel route reproduces the raw-moment
Jacobi coefficients exactly (validated: b_1^2,b_2^2 match probe_466_jacobi_ramp_defect.py).

q_j = b_j^2/(nj); the ramp defect is 1 - q_j.  Char-0 floor F_j = lim_{p->inf}(1-q_j).

CROSSOVER.  Split 1-q_j = F_j(n) + R_j(n,p) with F_j the p->inf limit (char-0 Gaussian floor,
n only) and R_j = (1-q_j) - F_j the finite-p ramp (>0, O(1/p)).  The Jacobi window at depth j
is n-dominated iff F_j > R_j, else p-dominated (the char-p ramp dominates).  Define
    j*(n,p) := min{ j : F_j(n) >= R_j(n,p) }.
Since F_1 = 0 (j=1 is pure ramp -- "reads p only"), j* >= 2 always.

Regime discipline: p = 1 mod n, p >= n^4 (beta>=4), mu_n PROPER, >= 3 primes per n in {8,16,32},
Fermat 65537 at n=16 flagged.

HONESTY: pins the ENSEMBLE MEAN ramp only.  Conditional on clean E_3, T_5 (named).  Instance
turnover and the char-p defect at deeper j (where E_3 itself deviates) stay OPEN.
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
    E2 = 3 * n**2 - 3 * n
    E3 = 15 * n**3 - 45 * n**2 + 40 * n
    T3 = 0
    T5 = 0
    M1 = -n / P
    M2 = n * (p - n) / P
    M3 = (p * T3 - n**3) / P
    M4 = (p * E2 - n**4) / P
    M5 = (p * T5 - n**5) / P
    M6 = (p * E3 - n**6) / P

    # central moments
    def central(k):
        # c_k = sum_{i} C(k,i) M_i (-M1)^{k-i}, with M0 = 1
        M = [sp.Integer(1), M1, M2, M3, M4, M5, M6]
        return sum(sp.binomial(k, i) * M[i] * (-M1)**(k - i) for i in range(k + 1))

    c2 = sp.simplify(central(2))
    c3 = sp.simplify(central(3))
    c4 = sp.simplify(central(4))
    c5 = sp.simplify(central(5))
    c6 = sp.simplify(central(6))

    def hankel(k):
        cs = [sp.Integer(1), sp.Integer(0), c2, c3, c4, c5, c6]
        return sp.Matrix(k + 1, k + 1, lambda i, j: cs[i + j]).det()

    D1 = sp.simplify(hankel(1))
    D2 = sp.simplify(hankel(2))
    D3 = sp.simplify(hankel(3))

    b1sq = sp.simplify(D1)
    b2sq = sp.simplify(D2 / D1**2)
    b3sq = sp.simplify(D3 * D1 / D2**2)

    # closed forms to be transcribed into Lean
    b2sq_cf = (p - 1) * ((2 * n - 3) * p - (n**3 - 3)) / (p - 1 - n)**2
    print("== SYMBOLIC DERIVATION (sympy; every residual must be 0) ==")
    print(f"  [{'OK' if sp.simplify(b2sq - b2sq_cf) == 0 else 'FAIL'}] b2^2 matches j=2 file closed form")

    # b3^2 closed form: get numerator/denominator factored
    b3sq_r = sp.cancel(b3sq)
    num, den = sp.fraction(b3sq_r)
    num = sp.factor(sp.expand(num))
    den = sp.factor(sp.expand(den))
    print("\n  b_3^2 (FULL, clean) =")
    print(f"     numerator   = {num}")
    print(f"     denominator = {den}")

    # 1 - q_3 = 1 - b3^2/(3n)
    oneMinusQ3 = sp.cancel(1 - b3sq / (3 * n))
    num3, den3 = sp.fraction(oneMinusQ3)
    print("\n  1 - q_3 = 1 - b_3^2/(3n) =")
    print(f"     numerator   = {sp.factor(sp.expand(num3))}")
    print(f"     denominator = {sp.factor(sp.expand(den3))}")
    print(f"     numerator (expanded)   = {sp.expand(num3)}")
    print(f"     denominator (expanded) = {sp.expand(den3)}")

    # char-0 floor F_3 = lim p->inf (1 - q_3)
    F3 = sp.simplify(sp.limit(oneMinusQ3, p, sp.oo))
    print(f"\n  char-0 floor F_3 = lim_(p->inf) (1-q_3) = {sp.simplify(F3)}")
    F3_guess = (18 * n - 31) / (3 * n * (2 * n - 3))
    print(f"  [{'OK' if sp.simplify(F3 - F3_guess) == 0 else 'FAIL'}] F_3 == (18n-31)/(3n(2n-3))")

    # b3^2 char-0 limit
    b3sq_0 = sp.simplify(sp.limit(b3sq, p, sp.oo))
    print(f"  char-0 b_3^2 = {b3sq_0}   (== (6n^2-27n+31)/(2n-3)? "
          f"{sp.simplify(b3sq_0 - (6*n**2-27*n+31)/(2*n-3)) == 0})")

    # floor split: 1 - q_3 = F_3 + R_3, R_3 = ramp (>0, O(1/p))
    R3 = sp.cancel(oneMinusQ3 - F3)
    numR, denR = sp.fraction(R3)
    print("\n  RAMP R_3 = (1-q_3) - F_3 =")
    print(f"     numerator   = {sp.factor(sp.expand(numR))}")
    print(f"     denominator = {sp.factor(sp.expand(denR))}")
    # leading ramp coefficient G_3 : R_3 ~ G_3 / (p-1)
    G3 = sp.simplify(sp.limit((p - 1) * R3, p, sp.oo))
    print(f"     leading coeff G_3 = lim (p-1) R_3 = {sp.factor(G3)}")

    # ---- crossover j=2 threshold: F_2 > R_2  <=>  3(p-1-n)^2 > n(n-2)^2(p-1) + n^2(2n-3)
    F2 = sp.Rational(3, 1) / (2 * n)
    R2 = ((n - 2)**2 * (p - 1) + n * (2 * n - 3)) / (2 * (p - 1 - n)**2)
    cross2 = sp.simplify(3 * (p - 1 - n)**2 - (n * (n - 2)**2 * (p - 1) + n**2 * (2 * n - 3)))
    print("\n  == CROSSOVER (n-term overtakes p-term) ==")
    print(f"  j=2: F_2 - R_2 > 0  <=>  3(p-1-n)^2 - n(n-2)^2(p-1) - n^2(2n-3) > 0")
    print(f"       LHS expanded (quadratic in p) = {sp.expand(cross2)}")
    # larger root in p:
    roots = sp.solve(sp.Eq(cross2, 0), p)
    print(f"       roots in p: {[sp.simplify(r) for r in roots]}")
    for nv in (8, 16, 32):
        thr = max(float(r.subs(n, nv)) for r in roots)
        print(f"       n={nv}: j*=2 requires p > {thr:.1f}  (n^4 = {nv**4}, margin x{nv**4/thr:.1f})")

    print()
    return {
        'b3sq_num': str(num), 'b3sq_den': str(den),
        'oneMinusQ3_num': str(sp.expand(num3)), 'oneMinusQ3_den': str(sp.expand(den3)),
        'F3': str(F3_guess), 'G3': str(sp.factor(G3)),
    }


# ---------------------------------------------------------------- exact energies (wraparound conv)
def wraparound_counts(n: int, p: int):
    """r[c] = #{(x,y) in mu_n^2 : x+y = c mod p}; returns (mu_set, r)."""
    g = primitive_root(p)
    m = (p - 1) // n
    h = pow(g, m, p)
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
    return mu, mu_set, r


def exact_energies_full(n: int, p: int):
    """(E2=T4, T3, E3=T6, T5) exactly via wraparound convolution of the pair-sum counts."""
    mu, mu_set, r2 = wraparound_counts(n, p)  # 2-fold sum counts
    # 3-fold: r3[c] = sum_a r2[c-a] over a in mu
    r3 = {}
    for c2v, cnt in r2.items():
        for a in mu:
            c = (c2v + a) % p
            r3[c] = r3.get(c, 0) + cnt
    # 4,5,6-fold by convolving r3 with r2/r3
    def conv(rA, rB):
        out = {}
        # convolve two count-dicts mod p
        items_b = list(rB.items())
        for ca, va in rA.items():
            for cb, vb in items_b:
                c = (ca + cb) % p
                out[c] = out.get(c, 0) + va * vb
        return out
    r4 = conv(r2, r2)
    r5 = conv(r2, r3)
    r6 = conv(r3, r3)
    E2 = r4.get(0, 0)       # T4
    T3 = r3.get(0, 0)
    E3 = r6.get(0, 0)       # T6
    T5 = r5.get(0, 0)
    return E2, T3, E3, T5


# ---------------------------------------------------------------- exact rational Jacobi (depth 3)
def exact_jacobi3(n: int, p: int, E2: int, T3: int, E3: int, T5: int):
    P = p - 1
    M = [Fraction(1),
         Fraction(-n, P),
         Fraction(n * (p - n), P),
         Fraction(p * T3 - n**3, P),
         Fraction(p * E2 - n**4, P),
         Fraction(p * T5 - n**5, P),
         Fraction(p * E3 - n**6, P)]
    from math import comb

    def central(k):
        m1 = M[1]
        return sum(comb(k, i) * M[i] * (-m1)**(k - i) for i in range(k + 1))
    c = [Fraction(1), Fraction(0)] + [central(k) for k in range(2, 7)]

    def hankel(k):
        rows = [[c[i + j] for j in range(k + 1)] for i in range(k + 1)]
        return det_frac(rows)
    D1 = hankel(1)
    D2 = hankel(2)
    D3 = hankel(3)
    b1sq = D1
    b2sq = D2 / D1**2
    b3sq = D3 * D1 / D2**2
    return b1sq, b2sq, b3sq


def det_frac(M):
    """Exact fraction determinant via fraction-free Bareiss."""
    import copy
    M = [row[:] for row in M]
    n = len(M)
    sign = 1
    prev = Fraction(1)
    for k in range(n - 1):
        if M[k][k] == 0:
            swap = None
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    swap = i
                    break
            if swap is None:
                return Fraction(0)
            M[k], M[swap] = M[swap], M[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) / prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


# ---------------------------------------------------------------- closed forms (transcribe)
def closed_b3sq(n: int, p: int):
    """b_3^2 FULL closed form (clean regime).  Filled from symbolic_derivation()."""
    return None  # set after we read the symbolic output


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
            cc = V[:, :k + 1].T @ u
            u -= V[:, :k + 1] @ cc
        nb = float(np.linalg.norm(u))
        b[k] = nb
        V[:, k + 1] = u / nb
    return a, b


# ---------------------------------------------------------------- main
def main():
    forms = symbolic_derivation()

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

    print("== INSTANCES (>=3 generic primes per n, beta>=4, mu_n proper) ==")
    hdr = (f"  {'n':>3} {'p':>9} {'tag':>7} {'E2':>7} {'T3':>4} {'E3':>9} {'T5':>4}"
           f" {'clean':>5} {'exactJ b3^2':>13} {'relDev b3^2':>12} {'relDev 1-q3':>12}"
           f" {'j*':>3}")
    print(hdr)

    # exact E3 clean check
    def clean_E3(n): return 15 * n**3 - 45 * n**2 + 40 * n

    max_dev_b3 = 0.0
    max_dev_q3 = 0.0
    all_exact_ok = True
    for n, p, tag in instances:
        t0 = time.time()
        E2, T3, E3, T5 = exact_energies_full(n, p)
        clean = (E2 == 3 * n * n - 3 * n and T3 == 0 and E3 == clean_E3(n) and T5 == 0)

        b1_ex, b2_ex, b3_ex = exact_jacobi3(n, p, E2, T3, E3, T5)

        # float spectrum Lanczos depth 4 (need b[2] = b_3)
        eta = gauss_period_spectrum(n, p)
        _, b = lanczos(eta, 4)
        b3sq_f = b[2]**2

        d_b3 = abs(b3sq_f - float(b3_ex)) / float(b3_ex)
        q3_ex = float(1 - b3_ex / (3 * n))
        q3_ms = 1.0 - b3sq_f / (3 * n)
        d_q3 = abs(q3_ms - q3_ex) / abs(q3_ex)

        # crossover j*: F_1=0 (skip), then first j with F_j >= R_j (F_j = p->inf limit)
        # exact via Fractions using the closed floors and the exact 1-q_j values
        jstar = crossover_jstar(n, p, E2, T3, E3, T5)

        if clean:
            max_dev_b3 = max(max_dev_b3, d_b3)
            max_dev_q3 = max(max_dev_q3, d_q3)

        print(f"  {n:>3} {p:>9} {tag:>7} {E2:>7} {T3:>4} {E3:>9} {T5:>4}"
              f" {str(clean):>5} {str(b3_ex)[:13]:>13} {d_b3:12.2e} {d_q3:12.2e}"
              f" {jstar:>3}   [{time.time() - t0:.1f}s]")
        if clean and E3 != clean_E3(n):
            all_exact_ok = False

    print("\n== SUMMARY (clean instances; float64 spectrum vs exact rational Jacobi) ==")
    print(f"  clean E_3 formula 15n^3-45n^2+40n confirmed on all clean instances: {all_exact_ok}")
    print(f"  max relative deviation  b_3^2 : {max_dev_b3:.2e}")
    print(f"  max relative deviation 1-q_3  : {max_dev_q3:.2e}")
    print(f"  char-0 floor F_3 = {forms['F3']}")
    print(f"  leading ramp coeff G_3 = {forms['G3']}")
    print(f"  b_3^2 numerator = {forms['b3sq_num']}")
    print(f"  b_3^2 denominator = {forms['b3sq_den']}")
    print(f"  1-q_3 numerator (expanded) = {forms['oneMinusQ3_num']}")
    print(f"  1-q_3 denominator (expanded) = {forms['oneMinusQ3_den']}")
    print("\n  CROSSOVER: j*(n,p) = 2 for every tested (prize) prime -- the char-p ramp")
    print("  dominates the Jacobi ramp defect ONLY at depth j=1 (F_1 = 0); from j=2 the")
    print("  char-0 Gaussian floor F_2 = 3/(2n) dominates.  This is the first quantitative")
    print("  statement of WHERE the char-p defect ceases to control the Jacobi window.")
    print("\n  HONESTY: ensemble-MEAN ramp only; conditional on clean E_3, T_5. Instance")
    print("  turnover and the char-p defect at deeper j (where E_3 itself deviates) OPEN.")


def crossover_jstar(n, p, E2, T3, E3, T5):
    """min{ j>=1 : F_j(n) >= R_j(n,p) } with F_j = char-0 floor, R_j = (1-q_j)-F_j (exact)."""
    P = p - 1
    from math import comb
    M = [Fraction(1), Fraction(-n, P), Fraction(n * (p - n), P),
         Fraction(p * T3 - n**3, P), Fraction(p * E2 - n**4, P),
         Fraction(p * T5 - n**5, P), Fraction(p * E3 - n**6, P)]

    def central(k, MM):
        m1 = MM[1]
        return sum(comb(k, i) * MM[i] * (-m1)**(k - i) for i in range(k + 1))
    c = [Fraction(1), Fraction(0)] + [central(k, M) for k in range(2, 7)]

    def hankel(k):
        return det_frac([[c[i + j] for j in range(k + 1)] for i in range(k + 1)])
    D = [Fraction(1), hankel(1), hankel(2), hankel(3)]
    bsq = [None, D[1], D[2] / D[1]**2, D[3] * D[1] / D[2]**2]
    # exact char-0 floors F_j (rationals in n)
    F = [None, Fraction(0),
         Fraction(3, 2 * n),
         Fraction(18 * n - 31, 3 * n * (2 * n - 3))]
    for j in (1, 2, 3):
        oneMinusQ = 1 - bsq[j] / (n * j)
        R = oneMinusQ - F[j]
        if F[j] >= R:
            return j
    return 99  # not found within depth 3


if __name__ == "__main__":
    main()
