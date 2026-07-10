#!/usr/bin/env python3
"""Exact deformation census for the rate-1/4 half-predecessor at (n,k,q)=(12,3,13).

The standard two-block packing line meets twelve five-column syndrome spans,
one for each nonzero scalar.  This probe keeps one such support witness for
each prescribed scalar and tests every five-support at the unused scalar zero.

For each enlarged linear system it computes the exact kernel in the two
syndrome rows.  A witness is forced joint precisely when every kernel vector's
direction lies in that witness span.  If no witness were forced joint, the at
most q=13 proper joint subspaces could not cover the kernel over F_q, so a
single stack realizing all thirteen nonjoint witnesses would exist.  Thus the
test is exhaustive for deformations of this packing support pattern.
"""

from itertools import combinations

import numpy as np

from probe_half_radius_grassmann import (
    incidence_oracle,
    linear_combo,
    np_nullspace,
)


P = 13
N = 12
K = 3
E = 5


def constraint(rows, gamma):
    a = np.asarray(rows, dtype=np.int64) % P
    return np.concatenate([a, gamma * a % P], axis=1)


def run():
    domain, columns, records, count = incidence_oracle(N, K, P)
    record_rows = {tuple(support): rows for support, rows in records}

    block = set(range(N // 2))
    base = linear_combo(
        [x * x % P if i in block else 0 for i, x in enumerate(domain)],
        columns,
        P,
    )
    direction = linear_combo(
        [x if i in block else 0 for i, x in enumerate(domain)],
        columns,
        P,
    )
    certificate = count(base, direction, certificate=True)
    assert set(certificate) == set(range(1, P))

    packing = {gamma: tuple(supports[0])
               for gamma, supports in certificate.items()}
    base_matrix = np.concatenate(
        [constraint(record_rows[support], gamma)
         for gamma, support in sorted(packing.items())],
        axis=0,
    )
    base_kernel = np_nullspace(base_matrix, P)

    histogram = {}
    forced_histogram = {}
    counterexample = None
    for support in combinations(range(N), E):
        rows = list(sorted(packing.items())) + [(0, support)]
        matrix = np.concatenate(
            [constraint(record_rows[witness], gamma)
             for gamma, witness in rows],
            axis=0,
        )
        kernel = np_nullspace(matrix, P)
        dim = len(kernel)
        histogram[dim] = histogram.get(dim, 0) + 1

        direction_basis = kernel[:, N - K:]
        forced = []
        for gamma, witness in rows:
            checks = np.asarray(record_rows[witness], dtype=np.int64)
            if not np.any(checks @ direction_basis.T % P):
                forced.append((gamma, witness))
        forced_histogram[len(forced)] = forced_histogram.get(len(forced), 0) + 1
        if not forced:
            counterexample = {
                "support": support,
                "kernel": kernel.tolist(),
                "packing": packing,
            }
            break

    result = {
        "p": P,
        "n": N,
        "k": K,
        "packing_count": len(certificate),
        "packing_base_nullity": len(base_kernel),
        "extension_kernel_histogram": histogram,
        "forced_joint_count_histogram": forced_histogram,
        "all_extensions_forced_joint": counterexample is None,
    }
    print(result)
    if counterexample is not None:
        print("COUNTEREXAMPLE", counterexample)
        return False
    return True


if __name__ == "__main__":
    raise SystemExit(0 if run() else 1)
