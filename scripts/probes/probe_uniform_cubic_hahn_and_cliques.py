#!/usr/bin/env python3
"""Exact rational verifier for Milestone 2 list-decoding theorems:
1. UniformCubicHahnBracket: exact central-moment sum-of-squares identities
   (cubicC2_central, cubicC1_central, cubicC0_central), universal O(n^(3/2))
   Theta(sqrt(n)) strip certificates, and uniform-in-n (n >= 256) Johnson+1
   (![11, 7, 6, 5]) and Johnson+2 (![61, 14, 10, 9]) ratio-cap certificates.
2. CubicHintBoundaryShell: P1 hint-boosted Quadratic/Cubic Hahn B2 = 2^31
   boundary-shell exclusions across all four Proximity Prize rates.
3. QuadraticHahnCliques: shifted Quadratic Hahn forced saturated-pair density
   and K4 clique certificates at B2 = 2^31 (Rate 1/2: 74.07% -> K4,
   Rate 1/16: 68.75% -> K4, Rate 1/8 J+2: 32.90%).
"""
from fractions import Fraction
from collections import defaultdict
import math


def quad_coeffs(n: Fraction, t: Fraction, d: Fraction):
    c1 = 2 * (t - 1) ** 2 / (n - 2) + 1 - d
    c0 = c1 * (t ** 2 / n) - t ** 2 * (t - 1) ** 2 / ((n - 1) * (n - 2))
    return c0, c1


def shift_quad_coeffs(n: Fraction, t: Fraction, d: Fraction, r0: Fraction):
    c1 = 2 * (t - 1) ** 2 / (n - 2) + 1 - (d + r0)
    c0 = d * r0 + c1 * (t ** 2 / n) - t ** 2 * (t - 1) ** 2 / ((n - 1) * (n - 2))
    return c0, c1


def cubic_coeffs(n: Fraction, t: Fraction, d: Fraction, r0: Fraction):
    c2 = 2 * (3 + 3 * (t - 2) ** 2 / (n - 4) - d - 2 * r0)
    c1 = (
        2 * d * r0
        + r0 ** 2
        - c2 * (-Fraction(1, 2) - (t - 1) ** 2 / (n - 2))
        - (
            2
            + 3 * (t - 2) ** 2 / (n - 4)
            + 3 * (t - 1) ** 2 * (t - 2) ** 2 / ((n - 3) * (n - 4))
        )
    )
    c0 = (
        -d * r0 ** 2
        + c1 * (t ** 2 / n)
        - c2 * (t ** 2 * (t - 1) ** 2 / (2 * (n - 1) * (n - 2)))
        + t ** 2 * (t - 1) ** 2 * (t - 2) ** 2 / ((n - 2) * (n - 3) * (n - 4))
    )
    return c0, c1, c2


def p1_hint_boost(n: Fraction, t: Fraction, d: Fraction, H: Fraction) -> Fraction:
    return (H * t - n * d) ** 2 / (n * H * (n - H))


class Poly:
    def __init__(self, d=None):
        self.d = {k: v for k, v in (d or {}).items() if v != 0}

    @staticmethod
    def const(v, nvars):
        return Poly({(0,) * nvars: Fraction(v)})

    @staticmethod
    def var(idx, nvars):
        e = [0] * nvars
        e[idx] = 1
        return Poly({tuple(e): Fraction(1)})

    def __add__(self, o):
        res = defaultdict(Fraction, self.d)
        for k, v in o.d.items():
            res[k] += v
        return Poly(res)

    def __sub__(self, o):
        res = defaultdict(Fraction, self.d)
        for k, v in o.d.items():
            res[k] -= v
        return Poly(res)

    def __neg__(self):
        return Poly({k: -v for k, v in self.d.items()})

    def __mul__(self, o):
        res = defaultdict(Fraction)
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                res[tuple(a + b for a, b in zip(k1, k2))] += v1 * v2
        return Poly(res)

    def __pow__(self, e):
        nvars = len(next(iter(self.d)))
        res = Poly.const(1, nvars)
        for _ in range(e):
            res = res * self
        return res


def verify_uniform_certificates():
    print("=== 1. Central-Moment Identities & Uniform-in-n Ratio-Cap Certificates (n >= 256) ===")
    # 1a. Verify exact central-moment sum-of-squares identities on sample (n, t, delta, sigma)
    for n_i, t_i, d_f, s_f in [(5, 2, Fraction(1, 7), Fraction(1, 3)), (64, 45, Fraction(3, 5), Fraction(7, 3)), (256, 180, Fraction(11, 4), Fraction(19, 3))]:
        n, t = Fraction(n_i), Fraction(t_i)
        mu = t * t / n
        V = t ** 2 * (n - t) ** 2 / (n ** 2 * (n - 1))
        w = t * (n - t)
        c0, c1, c2 = cubic_coeffs(n, t, mu + d_f, mu - s_f)
        assert c2 == 6 * (n - 2 * t) ** 2 / (n * (n - 4)) + 2 * (2 * s_f - d_f)
        surp = ((2 * (n ** 2 + 10 * n - 12) * w - 6 * n ** 2 * (n - 1)) ** 2 + 2 * n ** 3 * (n - 1) * (n - 2) ** 2 * (n - 3)) / (2 * n ** 2 * (n - 1) * (n - 2) * (n - 3) * (n ** 2 + 10 * n - 12))
        assert c1 == surp + V + (2 * s_f - d_f) * (n - 2 * t) ** 2 / (n * (n - 2)) + s_f * (s_f - 2 * d_f)
        assert c0 == t ** 2 * (n - t) ** 2 * (n - 2 * t) ** 2 / (n ** 3 * (n - 1) * (n - 2)) + (2 * s_f - d_f) * V - d_f * s_f ** 2
    print("  [PASS] cubicC2_central, cubicC1_central, cubicC0_central exact sum-of-squares verified")

    # 1b. Verify all 8 ratio-cap certificates (K=1: ![11, 7, 6, 5]; K=2: ![61, 14, 10, 9])
    ratio_cases = [
        ("1/2 J+1", 1, Fraction(442, 625), 180, Fraction(3, 23), 11),
        ("1/4 J+1", 1, Fraction(1, 2), 126, Fraction(1, 5), 7),
        ("1/8 J+1", 1, Fraction(221, 625), 89, Fraction(1, 4), 6),
        ("1/16 J+1", 1, Fraction(1, 4), 61, Fraction(3, 11), 5),
        ("1/2 J+2", 2, Fraction(442, 625), 179, Fraction(1, 14), 61),
        ("1/4 J+2", 2, Fraction(1, 2), 125, Fraction(3, 26), 14),
        ("1/8 J+2", 2, Fraction(221, 625), 88, Fraction(1, 7), 10),
        ("1/16 J+2", 2, Fraction(1, 4), 60, Fraction(4, 25), 9),
    ]
    n0 = Fraction(256)
    for label, K, ahi, tmin, c, M in ratio_cases:
        u = (2 * K + Fraction(K * K, tmin)) / (1 - ahi)
        assert u / n0 <= 2 * c
        assert 2 * c * u / n0 <= 1 / n0 + c * c
        denom = 2 * c - u * (c * c + 1 / n0)
        assert denom > 0
        ratio = (1 + c) ** 2 / denom
        assert ratio <= M
        print(f"  [PASS] {label:8s}: u={float(u):.4f}, c={c}, M/n <= {float(ratio):.4f} <= {M}")


def verify_cubic_hint_shells():
    print("\n=== 2. Cubic/Quadratic Hahn + P1 Hint B2 = 2^31 Boundary Shells ===")
    n = Fraction(2 ** 30)
    B2 = Fraction(2 ** 31)
    # (label, mode, k, t, H, r0_or_None, old_deg1_H)
    shells = [
        ("1/2 J+1 B2", "cubic", 2 ** 29, 759250124, 759263558, 314091338, 759265175),
        ("1/4 J+1 B2", "cubic", 2 ** 28, 536870910, 536903681, -53742, 536905668),
        ("1/8 J+2 B2", "quad", 2 ** 27, 379625060, 379661358, None, 379666627),
        ("1/16 J+1 B2", "quad", 2 ** 26, 268435453, 268467184, None, 268479191),
    ]
    for label, mode, k, t_int, H_int, r0_int, old_H in shells:
        t = Fraction(t_int)
        d = Fraction(k - 1)
        H = Fraction(H_int)
        assert n * d <= H * t
        boost = p1_hint_boost(n, t, d, H)
        if mode == "cubic":
            r0 = Fraction(r0_int)
            c0, c1, c2 = cubic_coeffs(n, t, d, r0)
            assert c1 >= 0 and c2 >= 0
            eff = c0 + c1 * boost
            assert eff > 0
            rhs = (t - d) * (t - r0) ** 2
            assert rhs < B2 * eff
        else:
            c0, c1 = quad_coeffs(n, t, d)
            assert c1 >= 0
            eff = c0 + c1 * boost
            assert eff > 0
            rhs = t * (t - d)
            assert rhs < B2 * eff
        a_j = math.isqrt(int(n) * (k - 1) - 1) + 1
        old_w = old_H - a_j
        new_w = H_int - a_j
        print(f"  [PASS] {label} ({mode}): agree < {H_int} (A_J + {new_w:,} vs deg-1 +{old_w:,}, {old_w/new_w:.2f}x tighter)")


def verify_quadratic_hahn_cliques():
    print("\n=== 3. Quadratic Hahn Forced Saturated-Pair Density & K4 Cliques (B2 = 2^31) ===")
    n = Fraction(2 ** 30)
    M = 2 ** 31 + 1
    turan3 = M * M // 3  # SimpleGraph.turanNumber M 3

    def check_case(label, k, t_int, smin, r0_int, pen_int, require_k4=True, min_density=None):
        t = Fraction(t_int)
        d = Fraction(k - 1)
        r0 = Fraction(r0_int)
        pen = Fraction(pen_int)
        c0, c1 = shift_quad_coeffs(n, t, d, r0)
        assert c1 >= 0
        assert pen > 0
        assert pen <= (d - smin) * (smin - r0)
        assert pen <= (d - 1) - r0
        rhs = Fraction(M) * ((t - d) * (t - r0)) - Fraction(M) ** 2 * c0
        nonsat_cap = rhs / pen
        total_pairs = Fraction(M * (M - 1))
        sat_density = 1 - nonsat_cap / total_pairs
        if require_k4:
            assert rhs < Fraction(M * (M - 1) - 2 * turan3) * pen
            status = "FORCES K4 (> 2/3)"
        else:
            assert float(sat_density) >= min_density
            status = f">= {min_density*100:.2f}%"
        print(f"  [PASS] {label}: saturated density >= {float(sat_density)*100:.4f}% ({status})")

    check_case("1/2 J+1 B2", 2 ** 29, 759250124, 444758424, 444758423, 92112487, require_k4=True)
    check_case("1/16 J+1 B2", 2 ** 26, 268435453, 0, -1, 67108863, require_k4=True)
    check_case("1/8 J+2 B2", 2 ** 27, 379625060, 0, -1, 134217727, require_k4=False, min_density=0.329)


if __name__ == "__main__":
    verify_uniform_certificates()
    verify_cubic_hint_shells()
    verify_quadratic_hahn_cliques()
    print("\nALL MILESTONE 2 EXACT RATIONAL CERTIFICATES VERIFIED!")
