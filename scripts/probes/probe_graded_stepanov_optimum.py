#!/usr/bin/env python3
"""Verify the optimal degree/multiplicity floor for graded rectangular Stepanov weights."""

from math import isqrt


def verify() -> None:
    n = 2**30
    a, b, c, d = 1_049_601, 2_043, 1_023, 1_046_527
    assert a * c <= n and d * (a + d - 1) < b * a * c
    assert a - 1 + n * (c - 1) <= 2**40 and d <= 2**40
    cap = (a - 1 + n * (b + c - 2)) // d
    assert cap == 3_143_679

    # A better floor requires degree < cap*D. Since D² <= B*A*C <= B*n,
    # this requires n*(B+C-2)² < B*cap². B >= 10001 contradicts this
    # by (B-1)²/B >= B-2. C >= 2502 contradicts it by
    # (B+C-2)² >= 4*B*(C-2).
    assert cap**2 < 9_999 * n
    candidates = 0
    for c in range(1, 2_502):
        a_max = n // c
        for b in range(1, 10_001):
            base_degree = n * (b + c - 2)
            d_min = base_degree // cap + 1
            variables = b * c * a_max
            # Feasibility D*(A+D-1) < B*C*A improves monotonically
            # with A whenever B*C>D, which feasibility itself requires.
            if d_min * (a_max + d_min - 1) >= variables:
                continue
            discriminant = (a_max - 1) ** 2 + 4 * (variables - 1)
            d_max = (isqrt(discriminant) - (a_max - 1)) // 2
            for d in range(d_min, d_max + 1):
                assert b * c > d
                a_min = d * (d - 1) // (b * c - d) + 1
                candidates += 1
                assert a_min <= a_max
                assert a_min - 1 + base_degree >= cap * d, (a_min, b, c, d)

    print(f"Optimal graded rectangular bound at n={n}: {cap} matched sites")
    print(f"Remaining integer candidates tested after bounding D: {candidates}")


if __name__ == "__main__":
    verify()
