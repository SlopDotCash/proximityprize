#!/usr/bin/env python3
"""#466 R324: refute a uniform spectral gap from the repeated-root 2-adic quotient.

For a=2^s, the coefficient vectors of (1+t)^j mod (2,t^a), 0<=j<a,
form the mod-2 Pascal matrix.  It is triangular and invertible, so an additive
character can realize any sign pattern on this orbit.  In particular one minus
sign and a-1 plus signs give normalized bias 1-2/a, approaching one.
"""

from __future__ import annotations

import math

import numpy as np


def pascal_mod2(a: int) -> np.ndarray:
    return np.array([[math.comb(j, k) & 1 for k in range(a)] for j in range(a)], dtype=np.uint8)


def rank_mod2(matrix: np.ndarray) -> int:
    work = matrix.copy()
    row = 0
    for col in range(work.shape[1]):
        pivot = next((i for i in range(row, work.shape[0]) if work[i, col]), None)
        if pivot is None:
            continue
        work[[row, pivot]] = work[[pivot, row]]
        for i in range(work.shape[0]):
            if i != row and work[i, col]:
                work[i] ^= work[row]
        row += 1
    return row


def solve_mod2(matrix: np.ndarray, target: np.ndarray) -> np.ndarray:
    augmented = np.concatenate((matrix.copy(), target[:, None]), axis=1)
    a = matrix.shape[0]
    for col in range(a):
        pivot = next(i for i in range(col, a) if augmented[i, col])
        augmented[[col, pivot]] = augmented[[pivot, col]]
        for i in range(a):
            if i != col and augmented[i, col]:
                augmented[i] ^= augmented[col]
    return augmented[:, -1]


def main() -> int:
    print("# R324 repeated-root local spectral-gap refutation")
    for a in (2, 4, 8, 16, 32):
        matrix = pascal_mod2(a)
        rank = rank_mod2(matrix)
        target = np.zeros(a, dtype=np.uint8)
        target[0] = 1
        character = solve_mod2(matrix, target)
        realized = matrix @ character % 2
        assert np.array_equal(realized, target)
        bias = int(np.where(realized == 0, 1, -1).sum())
        print(
            f"a={a:2d} rank={rank:2d} one_negative_bias={bias:2d} "
            f"normalized={bias/a:.9f} spectral_gap={1-bias/a:.9f}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
