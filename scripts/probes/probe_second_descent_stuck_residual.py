#!/usr/bin/env python3
"""Exact arithmetic companion to _SecondDescentStuckResidualRefuted.lean."""

import json


def interpolation_value(x):
    return x**3 - 35 * x**2 + 574 * x + 720


def factor_value(x):
    return (x - 1) * (x - 4) * (x - 9) * (x - 16) * (x**2 - 40 * x + 900)


def multiply_coefficients(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def main():
    nodes = (1, 4, 9, 16)
    scale = 1260
    # Ascending coefficients certify the identity for every integer x.
    witness = [720, 574, -35, 1]
    squared_equation = multiply_coefficients(witness, witness)
    squared_equation[1] -= scale**2
    factorization = [1]
    for root in nodes:
        factorization = multiply_coefficients(factorization, [-root, 1])
    factorization = multiply_coefficients(factorization, [900, -40, 1])
    assert squared_equation == factorization
    sparse_head = [1632, 0, -257, 5]
    sparse_odd = [2200, -820]
    sparse_equation = multiply_coefficients(sparse_head, sparse_head)
    for i, value in enumerate(multiply_coefficients(sparse_odd, sparse_odd)):
        sparse_equation[i + 1] -= value
    sparse_factorization = [1]
    for root in nodes:
        sparse_factorization = multiply_coefficients(sparse_factorization, [-root, 1])
    sparse_factorization = multiply_coefficients(sparse_factorization, [4624, -1820, 25])
    assert sparse_equation == sparse_factorization
    for x in range(-32, 33):
        assert interpolation_value(x)**2 - x * scale**2 == factor_value(x)
    assert all(interpolation_value(x)**2 == x * scale**2 for x in nodes)
    moduli = (17, 257, 65537, 2147483647, 2**61 - 1, 2**127 - 1)
    rows = []
    for p in moduli:
        assert len({x % p for x in nodes}) == 4
        assert scale % p != 0
        assert all((interpolation_value(x)**2 - x * scale**2) % p == 0 for x in nodes)
        assert all((2200 - 820 * x) % p != 0 for x in nodes)
        assert all(((5*x**3 - 257*x**2 + 1632)**2
                    - x*(2200 - 820*x)**2) % p == 0 for x in nodes)
        rows.append({"modulus": p, "distinct_roots": 4, "claimed_cap": 3,
                     "sparse_head_eligible_roots": 4})

    def finite_value(x):
        return (4 + 11 * x**2 + 7 * x**3) % 17

    def finite_odd_value(x):
        return (x + 4) % 17

    roots = {x for x in range(1, 17)
             if (finite_value(x)**2 - x * finite_odd_value(x)**2) % 17 == 0}
    assert roots == {1, 2, 4, 8}
    assert all(finite_odd_value(x) != 0 for x in roots)
    subgroup = {x for x in range(1, 17) if pow(x, 8, 17) == 1}
    assert len(subgroup) == 8
    assert roots <= subgroup
    assert all((-x) % 17 not in roots for x in roots)
    print(json.dumps({
        "status": "PASS",
        "target": "SecondDescentStuckResidual",
        "k": 2,
        "integer_identity_coefficients": squared_equation,
        "sparse_head_identity_coefficients": sparse_equation,
        "integer_identity_samples": 65,
        "field_sweep": rows,
        "zmod17_isolated_mu8_roots": sorted(roots),
        "zmod17_mu8_cardinality": len(subgroup),
        "scope": "Recorded universal residual refuted. Production Delta Star remains open.",
    }, indent=2))


if __name__ == "__main__":
    main()
