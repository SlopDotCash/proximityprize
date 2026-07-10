#!/usr/bin/env python3
"""Exact P1 certificate for the common-factor hole/triple trade.

The maximally thickened rate-quarter construction has one hole, no triple
core, and three proper pair cells of size 3m.  For an integer d, choose d
private coordinates from line 0 and d from line 1, multiply every nonzero
line factor by their degree-2d locator G, and move d private coordinates of
line 2 into the hole.  The cell ledger becomes

    holes=d+1, triple=2d, proper_pair=3m,
    singleton_each=7r+2-d,

so every core grows by d while the one-fresh scalar count remains n+2.

This probe checks the actual P1 modular arithmetic for the isolated hole
labels.  It searches a received pair (alpha*x,beta) independently at every
hole so that the three labels

    gamma_i = x * (h_i(x)-alpha)/(beta-h_i(x))

are distinct, lie outside mu_n, and avoid every label chosen earlier.  It
also verifies the pointwise agreement equation and the exact degree/count
ledger.  The default d=1 certifies the first lattice beyond the previously
reported maximal thickening.
"""

from __future__ import annotations

import sys

from probe_rate_quarter_prize_p1_isolated_counterexample import (
    G as DOMAIN_GENERATOR,
    K,
    M,
    N,
    P,
    add,
    eval_poly,
    inv,
    locator,
    scale,
)


def main() -> None:
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    r = (M - 1) // 3
    assert M == 3 * r + 1
    max_d = (M - 2) // 2
    max_holes = max_d + 1
    # Uniform greedy bound for the kernel-checked one-hole avoidance lemma.
    # At any stage the forbidden set has at most n+3*max_holes elements.
    general_avoidance_bound = 3 * (N + 3 * max_holes) + 1
    assert 2 * max_d + 2 == M
    assert max_d <= 7 * r + 2
    assert 3 * M + 2 * max_d + 1 == 4 * M - 1
    assert general_avoidance_bound < P
    assert 1 <= d <= r
    assert 3 * M + 2 * d + 1 < K

    zeta = pow(DOMAIN_GENERATOR, M, P)
    a_exp = {0, 1, 8}
    b_exp = {2, 9, 10}
    c_exp = {3, 5, 7}
    p_a = locator([pow(zeta, e, P) for e in sorted(a_exp)])
    p_b = locator([pow(zeta, e, P) for e in sorted(b_exp)])
    p_c = locator([pow(zeta, e, P) for e in sorted(c_exp)])
    lam = next(
        (p_c[j] - p_a[j]) * inv(p_b[j] - p_a[j]) % P
        for j in range(3)
        if p_a[j] != p_b[j]
    )
    assert p_c == add(scale(1 - lam, p_a), scale(lam, p_b))

    def factor_values(residue: int) -> list[int]:
        y = pow(zeta, residue, P)
        return [
            0,
            (1 - lam) * eval_poly(p_a, y) % P,
            eval_poly(p_c, y),
        ]

    def find_coset_parameters(
        residue: int, forbidden_labels: list[int] | None = None
    ) -> tuple[int, int, list[int]]:
        values = factor_values(residue)
        assert len(set(values)) == 3
        base_point = pow(DOMAIN_GENERATOR, residue, P)
        forbidden_labels = forbidden_labels or []
        for aa in range(1, 256):
            for bb in range(1, 256):
                if aa == bb or any(bb == t for t in values):
                    continue
                constants = [(t - aa) * inv(bb - t) % P for t in values]
                if any(c == 0 or pow(c, N, P) == 1 for c in constants):
                    continue
                if any(
                    pow(constants[i] * inv(constants[j]) % P, M, P) == 1
                    for i in range(3)
                    for j in range(i)
                ):
                    continue
                if any(
                    pow(delta * inv(c * base_point % P) % P, M, P) == 1
                    for delta in forbidden_labels
                    for c in constants
                ):
                    continue
                return aa, bb, constants
        raise AssertionError(f"no coset parameters for residue {residue}")

    y_hole = pow(zeta, 15, P)
    old_factor_values = factor_values(15)
    assert len(set(old_factor_values)) == 3

    # Quotient-fibre row parameters.  At a hole with common-locator value
    # ell, use alpha=ell*base_alpha and beta=ell*base_beta.  The ell factor
    # then cancels from gamma, recovering three fixed multiplicative cosets.
    base_alpha, base_beta, coset_constants = find_coset_parameters(15)

    def point(fibre_index: int) -> int:
        return pow(DOMAIN_GENERATOR, 15 + 16 * fibre_index, P)

    common_roots = (
        [point(j) for j in range(d)]
        + [point(r + j) for j in range(d)]
    )
    holes = [point(2 * r + j) for j in range(d)] + [point(3 * r)]
    assert len(set(common_roots + holes)) == 3 * d + 1
    assert all(pow(x, M, P) == y_hole for x in common_roots + holes)

    def common_locator_value(x: int) -> int:
        out = 1
        for root in common_roots:
            out = out * (x - root) % P
        return out

    assert all(common_locator_value(root) == 0 for root in common_roots)
    assert all(common_locator_value(x) != 0 for x in holes)

    labels: set[int] = set()
    hole_certificates: list[dict[str, object]] = []
    for x in holes:
        ell = common_locator_value(x)
        amplified_values = [ell * t % P for t in old_factor_values]
        assert len(set(amplified_values)) == 3
        alpha = ell * base_alpha % P
        beta = ell * base_beta % P
        gammas = [
            x * (h - alpha) * inv(beta - h) % P
            for h in amplified_values
        ]
        assert gammas == [x * c % P for c in coset_constants]
        assert len(set(gammas)) == 3
        assert all(pow(gamma, N, P) != 1 for gamma in gammas)
        assert all(gamma not in labels for gamma in gammas)
        for h, gamma in zip(amplified_values, gammas):
            assert (alpha * x + gamma * beta) % P == h * (x + gamma) % P
        labels.update(gammas)
        hole_certificates.append(
            {
                "x": x,
                "common_locator_value": ell,
                "factor_values": amplified_values,
                "base_alpha": base_alpha,
                "base_beta": base_beta,
                "alpha": alpha,
                "beta": beta,
                "gammas": gammas,
                "gamma_nth_powers": [pow(gamma, N, P) for gamma in gammas],
            }
        )

    hole_count = d + 1
    triple_count = 2 * d
    proper_pair_count = 3 * M
    singleton_count = 7 * r + 2 - d
    core_size = singleton_count + 2 * proper_pair_count + triple_count
    union_nondead = 3 * singleton_count + 3 * proper_pair_count
    isolated_labels = 3 * hole_count
    total_labels = union_nondead + isolated_labels
    threshold = core_size + 1
    radius_numerator = N - threshold

    assert hole_count + triple_count + union_nondead == N
    assert core_size == 8 * M + r + d
    assert total_labels == N + 2
    assert len(labels) == isolated_labels
    assert threshold == (25 * M + 2) // 3 + d
    assert radius_numerator == (23 * M - 2) // 3 - d

    # Saturated d=(m-2)/2 certificate without enumerating d points.  Take the
    # common roots from private quotient fibres 4 (line 0) and 11 (line 1),
    # and the new holes from private quotient fibre 13 (line 2).  All three
    # factor values are distinct on these private fibres, and max_d<m gives
    # enough points.  Scaled rows reduce every fibre-13 hole to one of three
    # fixed cosets.  The following exact m-th-power tests separate those full
    # cosets from mu_n, from each other, and from the three labels at the lone
    # residual fibre-15 hole.
    assert max_d < M
    assert all(len(set(factor_values(e))) == 3 for e in [4, 11, 13, 15])
    residual_x = pow(DOMAIN_GENERATOR, 15 + 16 * (3 * r), P)
    residual_labels = [residual_x * c % P for c in coset_constants]
    sat_alpha, sat_beta, sat_constants = find_coset_parameters(
        13, residual_labels
    )
    sat_base = pow(DOMAIN_GENERATOR, 13, P)
    assert all(pow(c, N, P) != 1 for c in sat_constants)
    assert all(
        pow(sat_constants[i] * inv(sat_constants[j]) % P, M, P) != 1
        for i in range(3)
        for j in range(i)
    )
    assert all(
        pow(delta * inv(c * sat_base % P) % P, M, P) != 1
        for delta in residual_labels
        for c in sat_constants
    )

    print(
        {
            "P": P,
            "n": N,
            "k": K,
            "m": M,
            "d": d,
            "max_d": max_d,
            "max_holes": max_holes,
            "general_avoidance_bound": general_avoidance_bound,
            "field_exceeds_general_avoidance_bound": P > general_avoidance_bound,
            "scaled_row_base_alpha": base_alpha,
            "scaled_row_base_beta": base_beta,
            "scaled_row_coset_constants": coset_constants,
            "saturated_agreement_threshold": (53 * M - 2) // 6,
            "saturated_radius_numerator": (43 * M + 2) // 6,
            "saturated_common_root_residues": [4, 11],
            "saturated_hole_residue": 13,
            "saturated_hole_base_alpha": sat_alpha,
            "saturated_hole_base_beta": sat_beta,
            "saturated_hole_coset_constants": sat_constants,
            "residual_hole_labels": residual_labels,
            "saturated_cross_fibre_ratio_mth_powers": [
                pow(delta * inv(c * sat_base % P) % P, M, P)
                for delta in residual_labels
                for c in sat_constants
            ],
            "common_factor_degree": 2 * d,
            "line_intercept_degree_bound": 3 * M + 2 * d + 1,
            "holes": hole_count,
            "triple_core": triple_count,
            "proper_pair_each": proper_pair_count,
            "singleton_each": singleton_count,
            "core_size": core_size,
            "agreement_threshold": threshold,
            "radius_numerator": radius_numerator,
            "nondead_owned_labels": union_nondead,
            "isolated_labels": isolated_labels,
            "total_labels": total_labels,
            "excess_over_n": total_labels - N,
            "hole_certificates": hole_certificates,
        }
    )


if __name__ == "__main__":
    main()
