#!/usr/bin/env python3
"""Exact falsify-first probes for lane DYN09 (dynamics / transfer operators).

Every calculation uses integers or Fraction.  The point is not to simulate the
production prime; it is to test whether the proposed dynamical mechanism has
enough information even in its abstract finite model.
"""

from fractions import Fraction
from itertools import product


def matmul(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def eye(n):
    return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]


def matpow(a, k):
    out = eye(len(a))
    for _ in range(k):
        out = matmul(out, a)
    return out


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def jacobi(b1, b2):
    return [
        [Fraction(0), Fraction(b1), Fraction(0)],
        [Fraction(b1), Fraction(0), Fraction(b2)],
        [Fraction(0), Fraction(b2), Fraction(0)],
    ]


def determinant3(a):
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )


def projection_matrix(parents):
    """Fine-to-fine sibling conditional expectation."""
    n = 2 * parents
    p = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(parents):
        for out_branch in range(2):
            for in_branch in range(2):
                p[2 * i + out_branch][2 * i + in_branch] = Fraction(1, 2)
    return p


def mv(a, x):
    return [sum(a[i][j] * x[j] for j in range(len(x))) for i in range(len(a))]


def l1_row_norm(a):
    return max(sum(abs(x) for x in row) for row in a)


def total_variation(p, q):
    return sum(abs(x - y) for x, y in zip(p, q)) / 2


def main():
    # 1. Toda / invariant-manifold gauge: a full exact trace test, beyond the
    # four low powers already used in the original tiny example.
    j50, j34 = jacobi(5, 0), jacobi(3, 4)
    trace_match = all(trace(matpow(j50, k)) == trace(matpow(j34, k)) for k in range(1, 13))
    print("1_toda_trace_match_k1_12", trace_match, "edge_readouts", 5, 4)

    # 2. Ruelle / sibling transfer: the induced fine-level operator is an
    # idempotent projection with L-infinity norm one and a mean-zero fixed point.
    p = projection_matrix(2)
    centered = [Fraction(1), Fraction(1), Fraction(-1), Fraction(-1)]
    print(
        "2_ruelle_projection",
        "idempotent", matmul(p, p) == p,
        "linf_norm", l1_row_norm(p),
        "centered_fixed", mv(p, centered) == centered,
    )

    # 3. Lyapunov cocycle: every word in two contracting-looking diagonal
    # matrices retains an invariant direction, so the worst exponent is zero.
    a0 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1, 2)]]
    a1 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1, 3)]]
    invariant = [Fraction(1), Fraction(0)]
    word_products_fix = True
    for word in product((0, 1), repeat=8):
        a = eye(2)
        for bit in word:
            a = matmul((a0, a1)[bit], a)
        word_products_fix &= mv(a, invariant) == invariant
    print("3_cocycle_worst_lyapunov_zero", word_products_fix, "words", 2**8)

    # 4. RG / bulk law: identical mass, mean and second moment do not determine
    # the extreme.  This is the exact bulk-versus-edge information loss.
    bulk_a = [Fraction(1), Fraction(0), Fraction(-1), Fraction(0)]
    bulk_b = [Fraction(3, 5), Fraction(4, 5), Fraction(-3, 5), Fraction(-4, 5)]
    stats = lambda x: (sum(x), sum(t * t for t in x), max(abs(t) for t in x))
    print("4_rg_same_mean_variance_different_edge", stats(bulk_a), stats(bulk_b))

    # 5. Haar packet: all fine detail coefficients can vanish while a centered
    # coarse mode survives with full amplitude.
    details = [centered[2 * i] - centered[2 * i + 1] for i in range(2)]
    coarse = [(centered[2 * i] + centered[2 * i + 1]) / 2 for i in range(2)]
    print("5_wavelet_zero_details_full_coarse", details, coarse)

    # 6. Dependent cascade: perfectly correlated siblings retain normalized
    # mass one at every depth; independence would predict square-root decay.
    cascade = {depth: 2**depth for depth in range(0, 13)}
    normalized = {depth: Fraction(mass, 2**depth) for depth, mass in cascade.items()}
    print("6_dependent_cascade_normalized", sorted(set(normalized.values())))

    # 7. Cat-map / ergodic analogy: the finite shift returns exactly, so its
    # correlation sequence has a hard recurrence rather than exponential decay.
    n = 16
    delta = [Fraction(int(i == 0)) for i in range(n)]
    correlations = []
    for k in range(n + 1):
        shifted = delta[-(k % n):] + delta[:-(k % n)] if k % n else delta[:]
        correlations.append(sum(x * y for x, y in zip(delta, shifted)))
    print("7_finite_shift_recurrence", correlations)

    # 8. Arithmetic QUE: before a full n-cycle, a point-orbit time average is
    # still far from uniform.  At T=n/2 the exact TV distance is 1/2.
    horizon = n // 2
    orbit_average = [Fraction(int(i < horizon), horizon) for i in range(n)]
    uniform = [Fraction(1, n) for _ in range(n)]
    print("8_que_half_orbit_tv", total_variation(orbit_average, uniform))

    # 9. Scattering / resonance: the two Jacobi matrices have the same exact
    # characteristic polynomial det(lambda I-J)=lambda^3-25lambda.
    for lam in (0, 1, 2, 5, 11):
        a = [[Fraction(lam) * int(i == j) - j50[i][j] for j in range(3)] for i in range(3)]
        b = [[Fraction(lam) * int(i == j) - j34[i][j] for j in range(3)] for i in range(3)]
        assert determinant3(a) == determinant3(b)
    print("9_scattering_same_resonance_different_local_edge", True)

    # 10. Thermodynamic pressure: identical absolute partition functions can
    # have maximal or zero signed sums.  Absolute pressure is phase-blind.
    depth = 12
    z_abs = 2**depth
    signed_aligned = sum(1 for _ in product((0, 1), repeat=depth))
    signed_balanced = sum((-1) ** sum(word) for word in product((0, 1), repeat=depth))
    print("10_pressure_phase_blind", "Zabs", z_abs, "aligned", signed_aligned, "balanced", signed_balanced)


if __name__ == "__main__":
    main()
