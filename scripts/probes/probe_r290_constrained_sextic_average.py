#!/usr/bin/env python3
"""R290: constrained sextic average diagnostics for the Jacobi triple-convolution energy.

R289 identified the exact lag hyperplane

    3*t + a + b == a' + b'  (mod m)

behind the R23 triple-convolution energy.  This probe computes the same energy three ways:

  * direct triple convolution;
  * nonzero six-tuple expansion;
  * lag-hyperplane expansion.

It also splits the six-tuple expansion by the collision partition of the three left indices
and three right indices.  The "perfect matching" bucket is the Wick diagonal x,y,z =
permutation(x',y',z'); everything else is connected/off-diagonal mass.
"""

from __future__ import annotations

import argparse
import itertools
import math
import random
from collections import defaultdict

import numpy as np
from sympy import isprime


def factor(x: int) -> list[int]:
    fs: list[int] = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            fs.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fs.append(x)
    return fs


def prim_root(p: int) -> int:
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // r, p) != 1 for r in fs):
            return g
    raise ValueError(f"no primitive root found for {p}")


def primes_1mod(modulus: int, count: int, start: int, limit: int) -> list[int]:
    out: list[int] = []
    x = max(start - start % modulus + 1, modulus + 1)
    while len(out) < count and x < limit:
        if isprime(x):
            out.append(x)
        x += modulus
    return out


def jacobi_coeffs(p: int, n: int) -> np.ndarray:
    g = prim_root(p)
    m = (p - 1) // n
    ind: dict[int, int] = {}
    x = 1
    for k in range(p - 1):
        ind[x] = k
        x = x * g % p

    ks = np.array([ind[a] for a in range(1, p)])
    chi = np.zeros(p)
    chi[1:] = np.where(ks % 2 == 0, 1.0, -1.0)

    J = np.zeros(m, dtype=complex)
    ts = np.arange(p)
    one_minus = (1 - ts) % p
    for j in range(m):
        lv = np.zeros(p, dtype=complex)
        lv[1:] = np.exp(2j * np.pi * j * n * ks / (p - 1))
        J[j] = np.sum(lv[ts] * chi[one_minus])
    return J


def triple_conv_energy(J: np.ndarray) -> tuple[float, np.ndarray]:
    m = len(J)
    self_conv = np.zeros(m, dtype=complex)
    for c in range(m):
        for j in range(1, m):
            k = (c - j) % m
            if k != 0:
                self_conv[c] += J[j] * J[k]
    triple = np.zeros(m, dtype=complex)
    for d in range(m):
        for j in range(1, m):
            triple[d] += self_conv[(d - j) % m] * J[j]
    return float(np.sum(np.abs(triple) ** 2).real), triple


def partition_shape(vals: tuple[int, ...]) -> tuple[int, ...]:
    counts: dict[int, int] = defaultdict(int)
    for v in vals:
        counts[v] += 1
    return tuple(sorted(counts.values(), reverse=True))


def permutation_count(shape: tuple[int, ...]) -> int:
    if shape == (3,):
        return 1
    if shape == (2, 1):
        return 3
    if shape == (1, 1, 1):
        return 6
    raise ValueError(f"unexpected triple collision shape {shape}")


def six_tuple_split_fast(J: np.ndarray) -> dict[str, complex]:
    """Exact constrained six-tuple split using per-sum/collision-shape aggregation.

    For each shape σ and residue d, let

        A_σ(d) = sum_{x+y+z=d, shape(x,y,z)=σ} J_x J_y J_z.

    Then the total contribution of left-shape σ and right-shape τ is

        sum_d A_σ(d) * conj(A_τ(d)).

    The Wick-perfect-matching bucket is computed separately by multiset: each unordered
    nonzero multiset contributes perm_count(shape)^2 * |J_x J_y J_z|^2.
    """
    m = len(J)
    nz = range(1, m)
    by_shape: dict[tuple[int, ...], np.ndarray] = {
        (1, 1, 1): np.zeros(m, dtype=complex),
        (2, 1): np.zeros(m, dtype=complex),
        (3,): np.zeros(m, dtype=complex),
    }
    wick = 0j
    for x in nz:
        for y in nz:
            for z in nz:
                shape = partition_shape((x, y, z))
                prod = J[x] * J[y] * J[z]
                by_shape[shape][(x + y + z) % m] += prod

    for x in nz:
        prod = J[x] ** 3
        wick += permutation_count((3,)) ** 2 * abs(prod) ** 2
    for x in nz:
        for y in range(x + 1, m):
            for repeated, single in ((x, y), (y, x)):
                prod = (J[repeated] ** 2) * J[single]
                wick += permutation_count((2, 1)) ** 2 * abs(prod) ** 2
    for x in nz:
        for y in range(x + 1, m):
            for z in range(y + 1, m):
                prod = J[x] * J[y] * J[z]
                wick += permutation_count((1, 1, 1)) ** 2 * abs(prod) ** 2

    buckets: dict[str, complex] = defaultdict(complex)
    buckets["wick_perfect_matching"] = wick
    shapes = [(1, 1, 1), (2, 1), (3,)]
    for lshape in shapes:
        for rshape in shapes:
            total = np.sum(by_shape[lshape] * np.conj(by_shape[rshape]))
            if lshape == rshape:
                # Remove the exact same-multiset contribution already assigned to Wick.
                same_shape_wick = 0j
                if lshape == (3,):
                    for x in nz:
                        same_shape_wick += permutation_count(lshape) ** 2 * abs(J[x] ** 3) ** 2
                elif lshape == (2, 1):
                    for x in nz:
                        for y in range(x + 1, m):
                            for repeated, single in ((x, y), (y, x)):
                                same_shape_wick += (
                                    permutation_count(lshape) ** 2
                                    * abs((J[repeated] ** 2) * J[single]) ** 2
                                )
                elif lshape == (1, 1, 1):
                    for x in nz:
                        for y in range(x + 1, m):
                            for z in range(y + 1, m):
                                same_shape_wick += (
                                    permutation_count(lshape) ** 2
                                    * abs(J[x] * J[y] * J[z]) ** 2
                                )
                total -= same_shape_wick
            buckets[f"connected_L{lshape}_R{rshape}"] += total
    return buckets


def wick_formula_one_small(m: int, q: int) -> float:
    """Closed Wick-perfect-matching bucket when nonzero coefficients contain one |J|^2=1
    coefficient and r=m-2 coefficients with |J|^2=q.

    Wick = Σ_unordered multiset M of size 3 perm(M)^2 Π_{i∈M}|J_i|^2.
    """
    r = m - 2
    if r < 0:
        return 0.0
    qf = float(q)
    total = 1.0 + r * qf**3
    total += 9.0 * (r * qf + r * qf**2 + r * (r - 1) * qf**3)
    total += 36.0 * ((r * (r - 1) / 2.0) * qf**2)
    if r >= 3:
        total += 36.0 * (r * (r - 1) * (r - 2) / 6.0) * qf**3
    return total


def six_tuple_split(J: np.ndarray, sample_left: int | None = None, seed: int = 0) -> dict[str, complex]:
    """Exact six-tuple expansion bucketed by collision/perfect-matching type."""
    m = len(J)
    buckets: dict[str, complex] = defaultdict(complex)
    nz = range(1, m)
    right_by_sum: dict[int, list[tuple[int, int, int, complex, tuple[int, ...]]]] = defaultdict(list)
    for xp, yp, zp in itertools.product(nz, repeat=3):
        d = (xp + yp + zp) % m
        right_by_sum[d].append((xp, yp, zp, np.conj(J[xp] * J[yp] * J[zp]), partition_shape((xp, yp, zp))))

    left_triples = list(itertools.product(nz, repeat=3))
    scale = 1.0
    if sample_left is not None and sample_left < len(left_triples):
        rng = random.Random(seed)
        left_triples = rng.sample(left_triples, sample_left)
        scale = ((m - 1) ** 3) / sample_left

    for x, y, z in left_triples:
        d = (x + y + z) % m
        left = J[x] * J[y] * J[z]
        lshape = partition_shape((x, y, z))
        lmulti = tuple(sorted((x, y, z)))
        for xp, yp, zp, rprod, rshape in right_by_sum[d]:
            if lmulti == tuple(sorted((xp, yp, zp))):
                key = "wick_perfect_matching"
            else:
                key = f"connected_L{lshape}_R{rshape}"
            buckets[key] += left * rprod
    if scale != 1.0:
        for key in list(buckets):
            buckets[key] *= scale
    return buckets


def lag_hyperplane_energy(J: np.ndarray) -> complex:
    """Exact lag-hyperplane expansion; O(m^5), suitable for small m sanity checks."""
    m = len(J)
    total = 0j
    for j in range(1, m):
        for t in range(m):
            x = (j + t) % m
            if x == 0:
                continue
            for a in range(m):
                y = (j + t + a) % m
                if y == 0:
                    continue
                for b in range(m):
                    z = (j + t + b) % m
                    if z == 0:
                        continue
                    left = J[x] * J[y] * J[z]
                    for ap in range(m):
                        yp = (j + ap) % m
                        if yp == 0:
                            continue
                        bp = (3 * t + a + b - ap) % m
                        zp = (j + bp) % m
                        if zp != 0:
                            total += left * np.conj(J[j] * J[yp] * J[zp])
    return total


def run_cell(
    p: int,
    n: int,
    lag_check_limit: int,
    sample_left: int | None,
    seed: int,
    summary: bool,
) -> dict[str, float]:
    J = jacobi_coeffs(p, n)
    m = len(J)
    e3, _triple = triple_conv_energy(J)
    buckets = (
        six_tuple_split(J, sample_left=sample_left, seed=seed)
        if sample_left is not None
        else six_tuple_split_fast(J)
    )
    bucket_total = sum(buckets.values())
    lag_total = lag_hyperplane_energy(J) if m <= lag_check_limit else None

    wick = buckets["wick_perfect_matching"].real
    wick_closed = wick_formula_one_small(m, p)
    connected = (bucket_total - buckets["wick_perfect_matching"]).real
    generic = buckets["connected_L(1, 1, 1)_R(1, 1, 1)"].real
    collision = connected - generic
    coll_21_21 = buckets["connected_L(2, 1)_R(2, 1)"].real
    coll_111_21 = (
        buckets["connected_L(1, 1, 1)_R(2, 1)"]
        + buckets["connected_L(2, 1)_R(1, 1, 1)"]
    ).real
    coll_cube = (
        buckets["connected_L(3,)_R(3,)"]
        + buckets["connected_L(3,)_R(2, 1)"]
        + buckets["connected_L(2, 1)_R(3,)"]
        + buckets["connected_L(3,)_R(1, 1, 1)"]
        + buckets["connected_L(1, 1, 1)_R(3,)"]
    ).real
    scale = (m**3) * (p**3)
    row = dict(
        p=float(p),
        n=float(n),
        m=float(m),
        beta=math.log(p) / math.log(n),
        e3=e3 / scale,
        wick=wick / scale,
        connected=connected / scale,
        generic=generic / scale,
        collision=collision / scale,
        coll_21_21=coll_21_21 / scale,
        coll_111_21=coll_111_21 / scale,
        coll_cube=coll_cube / scale,
        bucket_err=abs(e3 - bucket_total),
        wick_formula_err=abs(wick - wick_closed),
        lag_err=float(abs(e3 - lag_total)) if lag_total is not None else float("nan"),
    )
    if summary:
        print(
            f"{p:7d} {n:4d} {m:5d} {row['beta']:5.2f} "
            f"{row['e3']:9.4f} {row['wick']:9.4f} {row['generic']:+10.4f} "
            f"{row['collision']:+10.4f} {row['coll_21_21']:+10.4f} "
            f"{row['coll_111_21']:+10.4f} {row['coll_cube']:+9.4f} "
            f"{row['connected']:+10.4f}",
            flush=True,
        )
    else:
        print(
            f"p={p:>7} n={n:>3} m={m:>4} beta={row['beta']:.2f} "
            f"E3/scale={row['e3']:.4f} wick/scale={row['wick']:.4f} "
            f"conn/scale={row['connected']:+.4f} bucket_err={row['bucket_err']:.2e}"
            f" wick_formula_err={row['wick_formula_err']:.2e}"
            f"{' sampled' if sample_left is not None else ''}",
            flush=True,
        )
        if lag_total is not None:
            print(f"  lag_hyperplane_err={row['lag_err']:.2e}", flush=True)
        for key, val in sorted(buckets.items(), key=lambda kv: -abs(kv[1]))[:8]:
            print(f"  {key:32s} {val.real/scale:+.6f}", flush=True)
    return row


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", default="193:8,577:8,1153:16")
    parser.add_argument("--lag-check-limit", type=int, default=32)
    parser.add_argument("--sample-left", type=int, default=None)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--summary", action="store_true")
    args = parser.parse_args()
    if args.summary:
        print(
            f"{'p':>7} {'n':>4} {'m':>5} {'beta':>5} {'E3':>9} {'Wick':>9} "
            f"{'Generic':>10} {'Collision':>10} {'C21x21':>10} "
            f"{'C111x21':>10} {'Ccube':>9} {'Connected':>10}",
            flush=True,
        )
    for cell in args.cells.split(","):
        p_s, n_s = cell.split(":")
        run_cell(
            int(p_s),
            int(n_s),
            args.lag_check_limit,
            args.sample_left,
            args.seed,
            args.summary,
        )


if __name__ == "__main__":
    main()
