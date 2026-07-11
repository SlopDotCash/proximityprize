#!/usr/bin/env python3
"""G131 probe: additive-lift Capstone-A envelope at the arc saddle.

The G102F envelope for x = smallDiffPairs(C,W) is

    x^2 <= n*x + 4*rho*W*n^2.

To certify a terminal target x <= T from this envelope alone, the quadratic
constraint must exclude x = T+1.  This probe checks that witness and prints
the positive-root gap for small cells and the production-shaped window used
in _G131AdditiveLiftSaddleNoGo.lean.
"""

from math import log2, sqrt


def root_upper(n: int, rho: int, W: int) -> float:
    return (n + sqrt(n * n + 16 * rho * W * n * n)) / 2


def check(n: int, p: int, K: int, rho: int = 1) -> None:
    W = p // K
    T = (2 * n * n) // K
    x = T + 1
    rhs = n * x + 4 * rho * W * n * n
    root = root_upper(n, rho, W)
    print(
        f"n={n} p={p} K={K} W=2^{log2(W):.3f} rho={rho} "
        f"T={T} window_ok={4 * W < p} witness_Tplus1_ok={x * x <= rhs} "
        f"root/T={root / T:.6g} log2(root/T)={log2(root / T):.3f}"
    )


if __name__ == "__main__":
    cells = [
        (16, 257, 4, 1),
        (32, 1153, 5, 1),
        (64, 4289, 6, 1),
        (128, 17921, 9, 1),
        (2**30, 2**160, 2**13, 1),
        (2**30, 2**160, 2**14, 1),
    ]
    for row in cells:
        check(*row)
