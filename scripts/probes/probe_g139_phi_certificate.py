#!/usr/bin/env python3
"""Exact G139 Phi weak-Sidon certificate probe.

For an order-n subgroup H=<g> in F_p^*, define

    Phi_H(r) = (g^r - 1)^n,  1 <= r <= n/2.

Injectivity of Phi_H on 1 <= r <= n/2 certifies that H is weak Sidon under
unordered addition, modulo the forced antipodal zero-sum fiber.  Weak Sidon
then certifies that the normalized G139 equation

    a + b = c + 1,  a,b,c in H

has only the three lawful Mann families.

This is a finite exact-arithmetic probe, not a production n=2^30 closure and
not a proof that the first prime after round(n^(158/30)) always works.

The first three diagonal cells are found by exact first-prime search below
3317044064679887385961981, where Miller-Rabin with bases 2,3,5,...,37 is
deterministic.  The larger cells are explicit diagonal-scale primes whose
primality is checked by Pocklington from the included factorization of p-1.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json

BETA_NUM = 158
BETA_DEN = 30
DETERMINISTIC_MR_LIMIT = 3317044064679887385961981
MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
CERTIFIED_DIAGONAL_CELLS: tuple[tuple[int, int, tuple[int, ...]], ...] = (
    (
        65536,
        23269888444199867340881921,
        (2,) * 16 + (5, 7, 7, 13, 1061, 105072617218717),
    ),
    (
        131072,
        895816268326731990476390401,
        (2,) * 17 + (3, 3, 3, 5, 5, 10125238131224817239),
    ),
    (
        262144,
        34486060752854843021406240769,
        (2,) * 18 + (3, 3, 11, 17, 38299, 2344337, 870586793),
    ),
    (
        524288,
        1327603023409064462153689858049,
        (2,) * 19 + (1031, 3010541, 815821419738251),
    ),
    (
        1048576,
        51108469604461341804533103198209,
        (2,) * 20 + (13, 4871, 92369, 5292257, 1574578487),
    ),
)


@dataclass(frozen=True)
class PhiRow:
    label: str
    n: int
    p: int
    q: int
    generator: int
    domain_size: int
    image_size: int
    injective: bool
    collision_count: int
    collisions: tuple[tuple[int, int], ...]
    phi_image_sha256: str


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode() + b"\n"


def floor_nth_root(a: int, n: int) -> int:
    """Return floor(a^(1/n)) using integer arithmetic."""
    if a < 0 or n <= 0:
        raise ValueError("expected a >= 0 and n > 0")
    if a < 2:
        return a
    lo, hi = 1, 1
    while hi**n <= a:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**n <= a:
            lo = mid
        else:
            hi = mid
    return lo


def rounded_rational_power(n: int, num: int, den: int) -> int:
    """Return round(n^(num/den)) using exact integer comparisons."""
    base = n**num
    root = floor_nth_root(base, den)
    lower_gap = base - root**den
    upper_gap = (root + 1) ** den - base
    if upper_gap < lower_gap:
        return root + 1
    return root


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n >= DETERMINISTIC_MR_LIMIT:
        raise ValueError(f"n={n} exceeds deterministic Miller-Rabin limit for this probe")
    for p in MR_BASES:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    for a in MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def verify_prime_factorization(factors: tuple[int, ...]) -> None:
    for factor in set(factors):
        assert is_prime(factor), factor


def verify_pocklington_prime(p: int, factors: tuple[int, ...]) -> None:
    """Verify p is prime from the complete factorization of p-1."""
    verify_prime_factorization(factors)
    product = 1
    for factor in factors:
        product *= factor
    assert product == p - 1
    assert product * product > p

    for q in set(factors):
        for a in range(2, 200):
            if pow(a, p - 1, p) != 1:
                continue
            if gcd(pow(a, (p - 1) // q, p) - 1, p) == 1:
                break
        else:
            raise AssertionError(f"no Pocklington witness for q={q} at p={p}")


def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return abs(a)


def first_diagonal_prime(n: int) -> int:
    target = rounded_rational_power(n, BETA_NUM, BETA_DEN)
    q = max(1, target // n)
    if q % 2 == 0:
        q += 1
    elif n * q + 1 <= target:
        q += 2
    while True:
        p = n * q + 1
        if is_prime(p):
            return p
        q += 2


def order_n_generator(p: int, n: int) -> int:
    exponent = (p - 1) // n
    for base in range(2, 200):
        g = pow(base, exponent, p)
        if g != 1 and pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1:
            return g
    raise RuntimeError(f"no order-{n} generator found for p={p}")


def phi_certificate(n: int, p: int, label: str) -> PhiRow:
    assert (p - 1) % n == 0
    g = order_n_generator(p, n)

    powers = [1]
    x = 1
    for _ in range(1, n):
        x = (x * g) % p
        powers.append(x)
    assert (x * g) % p == 1
    assert len(set(powers)) == n

    phi_items: list[tuple[int, int]] = []
    seen: dict[int, int] = {}
    collisions: list[tuple[int, int]] = []
    for r in range(1, n // 2 + 1):
        phi_r = pow((powers[r] - 1) % p, n, p)
        phi_items.append((phi_r, r))
        if phi_r in seen:
            collisions.append((seen[phi_r], r))
        else:
            seen[phi_r] = r

    image_sorted = [str(v) for v, _ in sorted(phi_items)]
    return PhiRow(
        label=label,
        n=n,
        p=p,
        q=(p - 1) // n,
        generator=g,
        domain_size=n // 2,
        image_size=len(seen),
        injective=len(seen) == n // 2,
        collision_count=len(collisions),
        collisions=tuple(collisions),
        phi_image_sha256=hashlib.sha256(canonical(image_sorted)).hexdigest(),
    )


def emit_row(row: PhiRow) -> None:
    collision_text = ";".join(f"{a}:{b}" for a, b in row.collisions) or "-"
    print(
        f"{row.label},{row.n},{row.p},{row.q},{row.generator},"
        f"{row.domain_size},{row.image_size},{row.injective},"
        f"{row.collision_count},{collision_text},{row.phi_image_sha256}",
        flush=True,
    )


def main() -> None:
    rows: list[PhiRow] = []
    for n in (8192, 16384, 32768):
        p = first_diagonal_prime(n)
        assert is_prime(p)
        rows.append(phi_certificate(n, p, f"diagonal-n{n}"))
    for n, p, factors in CERTIFIED_DIAGONAL_CELLS:
        verify_pocklington_prime(p, factors)
        rows.append(phi_certificate(n, p, f"diagonal-n{n}"))
    assert is_prime(17318209)
    assert is_prime(138027521)
    rows.append(phi_certificate(64, 17318209, "G173-accident"))
    rows.append(phi_certificate(512, 138027521, "n512-offdiag-accident"))

    print(
        "label,n,p,q,generator,domain_size,image_size,injective,"
        "collision_count,collisions,phi_image_sha256",
        flush=True,
    )
    for row in rows:
        emit_row(row)

    assert all(row.injective for row in rows[:8])
    assert [row.collision_count for row in rows[8:]] == [3, 3]


if __name__ == "__main__":
    main()
