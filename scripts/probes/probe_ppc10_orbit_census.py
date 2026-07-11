#!/usr/bin/env python3
"""Proof-producing-discovery census for the first fully-disjoint Paley anchors.

The script works with an order-``n`` multiplicative subgroup of ``F_p^*``, where
``n`` is a power of two and ``p = 1 (mod n)`` is the first deterministic prime
searched from ``n^4``.  It enumerates *unordered* ``r``-words and attaches their
permutation-orbit sizes.  Sorting these representatives by their field sum gives
the exact ordered energy and exact ordered fully-disjoint census:

  E_s = sum_{left support s} w(left) * bucketMass(sum(left)),
  D_s = sum_{left support s} w(left) * disjointMass(left).

Thus the enumeration has ``binomial(n+r-1,r)`` records rather than ``n^r`` and
never uses floating point, FFT rounding, randomized hashes, or a solver.  The
canonical SHA-256 digest covers the sorted representative records.  The Lean
file ``_PPC10OrbitCensusCertificate.lean`` proves the weighted-bucket formulas
and kernel-checks the arithmetic interpretation of the strongest anchor.

Default cells deliberately stop at ``r=3`` for ``n=256,512`` and at ``r=4``
for ``n=128``.  The orbit count is Theta(n^r/r!), so this is an anchor falsifier,
not a production algorithm for ``(n,r)=(2^30,110)``.
"""

from __future__ import annotations

import argparse
import hashlib
import math
import subprocess
import sys
from dataclasses import dataclass

import numpy as np


MR_BASES_U64 = (2, 325, 9375, 28178, 450775, 9780504, 1795265022)
SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime_u64(n: int) -> bool:
    """Deterministic Miller--Rabin for ``n < 2^64``."""
    if n < 2:
        return False
    for q in SMALL_PRIMES:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES_U64:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def matched_prime(n: int) -> tuple[int, int]:
    """First ``p=n*k+1`` with even ``k >= n^3`` passing deterministic MR."""
    k = n**3
    if k % 2:
        k += 1
    while not is_prime_u64(n * k + 1):
        k += 2
    return n * k + 1, k


def subgroup(p: int, n: int) -> tuple[np.ndarray, int, int]:
    """Return powers of an element of exact order ``n`` (``n`` a 2-power)."""
    assert n > 1 and n & (n - 1) == 0 and (p - 1) % n == 0
    for base in range(2, 1000):
        zeta = pow(base, (p - 1) // n, p)
        if pow(zeta, n, p) == 1 and pow(zeta, n // 2, p) != 1:
            break
    else:
        raise RuntimeError("failed to find exact-order element")
    values, x = [], 1
    for _ in range(n):
        values.append(x)
        x = x * zeta % p
    assert x == 1 and len(set(values)) == n
    return np.asarray(values, dtype=np.uint64), zeta, base


def double_factorial_odd(r: int) -> int:
    return math.prod(range(1, 2 * r, 2))


def falling(n: int, s: int) -> int:
    return math.prod(range(n - s + 1, n + 1))


def support_populations(n: int, r: int) -> list[int]:
    """Ordered r-words with exactly s distinct coordinates, for r=3 or 4."""
    stirling = {3: (0, 1, 3, 1), 4: (0, 1, 7, 6, 1)}[r]
    return [falling(n, s) * stirling[s] for s in range(r + 1)]


def char_zero_energy(n: int, r: int) -> int:
    if r == 3:
        return 15 * n**3 - 45 * n**2 + 40 * n
    if r == 4:
        return 105 * n**4 - 630 * n**3 + 1435 * n**2 - 1155 * n
    raise ValueError(r)


@dataclass
class Records:
    sums: np.ndarray
    indices: np.ndarray
    weights: np.ndarray
    supports: np.ndarray


def enumerate_records(group: np.ndarray, p: int, r: int) -> Records:
    n = len(group)
    count = math.comb(n + r - 1, r)
    sums = np.empty(count, dtype=np.uint64)
    indices = np.empty((count, r), dtype=np.uint16)
    weights = np.empty(count, dtype=np.uint8)
    supports = np.empty(count, dtype=np.uint8)
    q = 0

    if r == 3:
        for i in range(n):
            for j in range(i, n):
                width = n - j
                sl = slice(q, q + width)
                sums[sl] = (int(group[i]) + int(group[j]) + group[j:]) % p
                indices[sl, 0] = i
                indices[sl, 1] = j
                indices[sl, 2] = np.arange(j, n, dtype=np.uint16)
                if i == j:
                    weights[sl], supports[sl] = 3, 2
                    weights[q], supports[q] = 1, 1
                else:
                    weights[sl], supports[sl] = 6, 3
                    weights[q], supports[q] = 3, 2
                q += width
    elif r == 4:
        for i in range(n):
            for j in range(i, n):
                for k in range(j, n):
                    width = n - k
                    sl = slice(q, q + width)
                    sums[sl] = (
                        int(group[i]) + int(group[j]) + int(group[k]) + group[k:]
                    ) % p
                    indices[sl, 0] = i
                    indices[sl, 1] = j
                    indices[sl, 2] = k
                    indices[sl, 3] = np.arange(k, n, dtype=np.uint16)
                    for offset, ell in enumerate(range(k, n)):
                        multiplicities = []
                        for value in (i, j, k, ell):
                            if multiplicities and multiplicities[-1][0] == value:
                                multiplicities[-1][1] += 1
                            else:
                                multiplicities.append([value, 1])
                        denominator = math.prod(math.factorial(c) for _, c in multiplicities)
                        weights[q + offset] = 24 // denominator
                        supports[q + offset] = len(multiplicities)
                    q += width
    else:
        raise ValueError("only r=3,4 are implemented")

    assert q == count
    order = np.argsort(sums, kind="stable")
    return Records(sums[order], indices[order], weights[order], supports[order])


def record_digest(records: Records) -> str:
    h = hashlib.sha256()
    for array in (records.sums, records.indices, records.weights, records.supports):
        h.update(array.astype(array.dtype.newbyteorder("<"), copy=False).tobytes())
    return h.hexdigest()


def census(n: int, r: int) -> None:
    p, cofactor = matched_prime(n)
    group, zeta, base = subgroup(p, n)
    records = enumerate_records(group, p, r)
    sums, indices = records.sums, records.indices
    weights, supports = records.weights, records.supports

    cuts = np.flatnonzero(np.r_[True, sums[1:] != sums[:-1], True])
    starts, ends = cuts[:-1], cuts[1:]
    sizes = ends - starts
    bucket_mass = np.add.reduceat(weights.astype(np.uint64), starts)
    energy = int(np.sum(bucket_mass.astype(object) ** 2))

    mass_at_record = np.repeat(bucket_mass, sizes)
    energy_by_support = [0]
    for s in range(1, r + 1):
        rows = supports == s
        energy_by_support.append(
            int(np.sum(weights[rows].astype(np.uint64) * mass_at_record[rows], dtype=np.uint64))
        )
    del mass_at_record

    disjoint, disjoint_by_support = 0, [0] * (r + 1)
    for bucket_index in np.flatnonzero(sizes > 1):
        start, end = int(starts[bucket_index]), int(ends[bucket_index])
        bucket_indices = indices[start:end]
        bucket_weights = weights[start:end].astype(np.uint64)
        bucket_supports = supports[start:end]
        is_disjoint = np.ones((end - start, end - start), dtype=bool)
        for i in range(r):
            for j in range(r):
                is_disjoint &= bucket_indices[:, i, None] != bucket_indices[None, :, j]
        pair_weights = bucket_weights[:, None] * bucket_weights[None, :]
        disjoint += int(np.sum(pair_weights[is_disjoint], dtype=np.uint64))
        for s in range(1, r + 1):
            left_rows = bucket_supports == s
            disjoint_by_support[s] += int(
                np.sum(pair_weights[left_rows, :][is_disjoint[left_rows, :]], dtype=np.uint64)
            )

    populations = support_populations(n, r)
    assert sum(populations) == n**r
    assert sum(energy_by_support) == energy
    assert sum(disjoint_by_support) == disjoint

    base_by_support, total_by_support, correction_by_support = [], [], []
    for s in range(r + 1):
        base_s = p * energy_by_support[s] - populations[s] * n**r
        total_s = p * disjoint_by_support[s] - populations[s] * (n - s) ** r
        base_by_support.append(base_s)
        total_by_support.append(total_s)
        correction_by_support.append(total_s - base_s)

    base_total = p * energy - n ** (2 * r)
    principal_disjoint = sum(populations[s] * (n - s) ** r for s in range(r + 1))
    total_centered = p * disjoint - principal_disjoint
    correction = total_centered - base_total
    assert sum(base_by_support) == base_total
    assert sum(total_by_support) == total_centered
    assert sum(correction_by_support) == correction
    assert total_centered == base_total + correction

    expected = char_zero_energy(n, r)
    wick = double_factorial_odd(r) * n**r
    digest = record_digest(records)
    print(f"CELL n={n} r={r} p={p} cofactor={cofactor} base={base} zeta={zeta}")
    print(
        f"  records={len(sums)} buckets={len(starts)} multiBuckets={int(np.count_nonzero(sizes > 1))} "
        f"maxBucket={int(sizes.max())} sha256={digest}"
    )
    print(
        f"  energy={energy} charZero={expected} excess={energy - expected} "
        f"wick={wick} wickSlack={wick - energy}"
    )
    print(
        f"  disjoint={disjoint} principalDisjoint={principal_disjoint} "
        f"baseCentered={base_total} disjointCentered={total_centered} correction={correction} "
        f"check={total_centered == base_total + correction}"
    )
    for s in range(1, r + 1):
        print(
            f"  support={s} A={populations[s]} E={energy_by_support[s]} "
            f"D={disjoint_by_support[s]} B={base_by_support[s]} "
            f"T={total_by_support[s]} C={correction_by_support[s]}"
        )


def parse_cell(raw: str) -> tuple[int, int]:
    try:
        n, r = map(int, raw.split(":"))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("cell must have form n:r") from exc
    if n <= 1 or n & (n - 1) or r not in (3, 4):
        raise argparse.ArgumentTypeError("n must be a power of two >1 and r must be 3 or 4")
    return n, r


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cell",
        type=parse_cell,
        action="append",
        help="census cell n:r; repeatable (defaults: 128:3, 256:3, 512:3, 128:4)",
    )
    args = parser.parse_args()
    if args.cell:
        for cell in args.cell:
            census(*cell)
    else:
        # Keep the peak resident set bounded: NumPy's allocator may retain the
        # n=512 arrays even after a cell returns, so each default cell gets a
        # fresh process.  The child has an explicit --cell and cannot recurse.
        for n, r in ((128, 3), (256, 3), (512, 3), (128, 4)):
            subprocess.run(
                [sys.executable, __file__, "--cell", f"{n}:{r}"],
                check=True,
            )
