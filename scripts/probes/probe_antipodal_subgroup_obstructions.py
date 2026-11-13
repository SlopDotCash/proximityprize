#!/usr/bin/env python3
"""Exact obstructions to two antipodal root-count repairs at the sponsor fields.

The existing _PrizeShapePrimeP30{,Second}.lean modules certify the primes and
generators below. This probe checks modular identities; it does not reprove
primality, run Lean, or establish the production Delta Star threshold.

One witness preserves the two-even-monomial head and low-degree tail but has
isolated roots in both halved-subgroup cosets. The other violates the recorded
IsolatedNonCosetCountResidual cap even with subgroup membership and exclusion
of every full nontrivial subcoset. The latter has no decoded-family certificate.
"""
# Copyright (c) 2026 Hardyzyt. All rights reserved.
# Released under the MIT and Apache 2.0 licenses. See LICENSE-MIT and LICENSE.

import json


N = 2**30
INSTANCES = (
    ("first", N * (2**128 + 192) + 1, 3,
     303645430271030343624574566109998498685964493478),
    ("second", N * (2 * 2**128 + 13) + 1, 37,
     192152681249815148642741928588691886362054863855),
)


def _require(condition, detail):
    """Keep the certificate checks active under Python optimization."""
    if not condition:
        raise AssertionError(detail)


def multiply(left, right, modulus):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = (result[i + j] + a * b) % modulus
    return result


def evaluate(coefficients, x, modulus):
    value = 0
    for coefficient in reversed(coefficients):
        value = (value * x + coefficient) % modulus
    return value


def mixed_coset_certificate(p, g):
    """Refute confinement with literal domain size and a valid sparse head."""
    k = N // 2
    b, a = k, k + 2
    gamma = -g * g % p
    tail = [(-g * g - g) % p, (g + 1) % p]
    _require(b % 2 == a % 2 == 0 and k <= b < a < N,
             "head exponents are not even and in range")
    _require(len(tail) - 1 < k and gamma != 0 and tail[1] != 0,
             "tail or head coefficient is invalid")

    def agreement(x):
        return (pow(x, a, p) + gamma * pow(x, b, p) - evaluate(tail, x, p)) % p

    def even_part(u):
        return (pow(u, a // 2, p) + gamma * pow(u, b // 2, p) - tail[0]) % p

    roots = [1, g]
    _require(len(set(roots)) == 2, "mixed-coset roots are not distinct")
    antipodes = [(-x) % p for x in roots]
    for x in roots + antipodes:
        _require(pow(x, N, p) == 1, "point is outside the evaluation domain")
        _require(agreement(x) == (even_part(x * x % p) - x * tail[1]) % p,
                 "even/odd split does not match the agreement")
    _require([agreement(x) for x in roots] == [0, 0],
             "isolated roots are not roots of the agreement")
    antipode_values = [agreement(x) for x in antipodes]
    _require(antipode_values == [2 * (g + 1) % p, 2 * g * (g + 1) % p],
             "antipode values do not match the closed form")
    _require(all(antipode_values), "an antipode is also a root")
    coset_values = [pow(x, N // 2, p) for x in roots]
    _require(coset_values == [1, p - 1],
             "roots are not in both halved-subgroup cosets")
    return {
        "code_dimension": k,
        "head_exponents": [a, b],
        "head_gamma": gamma,
        "tail_coefficients_ascending": tail,
        "isolated_roots": roots,
        "agreement_at_antipodes": antipode_values,
        "halved_order_powers": coset_values,
        "scope": "Two opposite cosets; no production-radius decoding claim.",
    }


def noncoset_count_certificate(p, g):
    """Refute the k=3 cap on the actual halved subgroup, without a full subcoset."""
    t = pow(g, N // 32, p)
    _require(pow(t, 32, p) == 1 and pow(t, 16, p) == p - 1,
             "t is not a primitive 32nd root of unity")
    lifts = [pow(t, i, p) for i in range(5)]
    roots = [x * x % p for x in lifts]
    _require(len(set(roots)) == 5, "noncoset roots are not distinct")
    _require(all(pow(u, N // 2, p) == 1 for u in roots),
             "a root is outside the halved subgroup")
    # Q(X)=product_i(X-t_i)=A(X^2)-X*O(X^2).
    q = [1]
    for x in lifts:
        q = multiply(q, [-x % p, 1], p)
    even, odd = q[::2], [-coefficient % p for coefficient in q[1::2]]
    _require(len(even) == len(odd) == 3 and even[-1] and odd[-1],
             "A or O has the wrong degree")
    squared_even = multiply(even, even, p)
    x_squared_odd = [0] + multiply(odd, odd, p)
    residual = [(a - b) % p for a, b in zip(squared_even + [0], x_squared_odd)]
    factored = [p - 1]
    for u in roots:
        factored = multiply(factored, [-u % p, 1], p)
    # A nonzero degree-five polynomial with this factorization has exactly these roots.
    _require(residual == factored, "residual does not factor over the roots")
    odd_values = [evaluate(odd, u, p) for u in roots]
    _require(all(odd_values), "O vanishes at a root")
    _require(all(evaluate(even, u, p) == x * value % p
                 for x, u, value in zip(lifts, roots, odd_values)),
             "A(u) != x * O(u) at a root")
    _require(all(evaluate(residual, u, p) == 0 for u in roots),
             "residual does not vanish at a root")
    _require(all((-u) % p not in roots for u in roots),
             "root set contains an antipodal pair")
    _require(all(evaluate(residual, (-u) % p, p) != 0 for u in roots),
             "residual vanishes at an antipode")
    # Every nontrivial subgroup of a cyclic 2-group contains -1. A complete coset
    # contains an antipodal pair, which the complete root set above excludes.
    k = 3
    _require(len(even) - 1 < k and len(odd) - 1 < k and len(roots) > k + 1,
             "root count does not exceed the claimed cap")
    return {
        "residual_k": k,
        "claimed_cap": k + 1,
        "complete_root_count": len(roots),
        "A_coefficients_ascending": even,
        "O_coefficients_ascending": odd,
        "residual_coefficients_ascending": residual,
        "roots": roots,
        "O_values_at_roots": odd_values,
        "root_subgroup_order": 16,
        "no_full_nontrivial_subcoset": True,
        "scope": "Subgroup/noncoset repair fails; no original decoded-head realization.",
    }


def main():
    certificates = []
    for name, p, base, g in INSTANCES:
        _require(p % 2 == 1 and (p - 1) % N == 0,
                 f"{name}: modulus is not 1 mod the domain order")
        _require(pow(base, (p - 1) // N, p) == g,
                 f"{name}: generator does not match the base")
        _require(pow(g, N, p) == 1 and pow(g, N // 2, p) == p - 1,
                 f"{name}: generator order is not the domain order")
        certificates.append({
            "field": name,
            "modulus": p,
            "domain_order": N,
            "generator": g,
            "mixed_coset": mixed_coset_certificate(p, g),
            "noncoset_count": noncoset_count_certificate(p, g),
        })
    print(json.dumps({"status": "PASS", "certificates": certificates}, indent=2))


if __name__ == "__main__":
    main()
