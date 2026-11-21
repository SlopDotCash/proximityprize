#!/usr/bin/env python3
"""Verify two finite counterexamples to the all-rate MCA bound e+1 at slack ≥3."""


def verify(p: int, order: int, k: int, e: int, add_zero: bool) -> None:
    domain = {x for x in range(1, p) if pow(x, order, p) == 1}
    if add_zero:
        domain.add(0)
    n = len(domain)
    scalars = {pow(x, e, p) for x in domain if x}
    if not (n == order + int(add_zero) and order % e == 0 and len(scalars) > e + 1):
        raise ValueError("Incorrect domain or too few fiber labels")
    if not (n - 2*e - (k - 1) >= 3 and n - 3*e < k <= n - 2*e < n - e):
        raise ValueError("Incorrect slack, witness degree, or root-count obstruction")
    for gamma in sorted(scalars):
        # First two monomials of (X^n - X^(n-order))/(X^e - gamma) are the rows.
        def quotient_tail(x: int) -> int:
            return sum(pow(gamma, j, p) * pow(x, n - (j+1)*e, p)
                       for j in range(2, order // e))

        agrees = {x for x in domain if (pow(x, n-e, p) + gamma * pow(x, n-2*e, p)
                                        + quotient_tail(x)) % p == 0}
        if agrees != {x for x in domain if pow(x, e, p) != gamma} or len(agrees) != n-e:
            raise ValueError(f"Incorrect witness for gamma={gamma}")
    print(f"F_{p}, n={n}, k={k}, e={e}: {len(scalars)} verified bad scalars, e+1={e+1}")


if __name__ == "__main__":
    verify(31, 15, 8, 3, True)
    verify(97, 32, 22, 4, False)
