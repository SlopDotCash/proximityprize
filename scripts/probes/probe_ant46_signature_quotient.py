#!/usr/bin/env python3
r"""Falsify-first audit of the ANT46 cyclotomic-unit signature quotient.

For the subgroup H of order n in F_p^*, define

    kappa(x) = (x - 1)^n,  x in H \ {1}.

The exact quotient proved in `_ANT46RungTwoAccidentOrbit.lean` says that accidents are
ordered kappa-collisions after deleting the diagonal y=x and inversion graph y=x^-1.
For a kappa-fibre of size k, with s=1 when it contains the self-inverse root -1 and s=0
otherwise, its contribution is therefore k^2 - 2k + s.

This probe:
  * checks that formula against independent O(n^2) triple enumeration at every bad prime;
  * exhibits explicit collision/triple witnesses;
  * falsifies naive uniform claims on small dyadic orders before production use;
  * verifies the n=8 canonical polynomial
        K_8(T)=T^3+120T^2-2160T-256,
    whose discriminant and value at 2^8 isolate the relevant bad primes 17 and 41.

Exit 0 means every exact identity/cross-check passed.  Finding bad primes is expected and
is reported as mathematical evidence, not as probe failure.
"""

from __future__ import annotations

from collections import defaultdict


LIMIT = 500_000
ORDERS = (4, 8, 16, 32, 64, 128)


def prime_sieve(limit: int) -> list[int]:
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[:2] = b"\x00\x00"
    for d in range(2, int(limit**0.5) + 1):
        if is_prime[d]:
            is_prime[d * d : limit + 1 : d] = b"\x00" * (((limit - d * d) // d) + 1)
    return [p for p in range(2, limit + 1) if is_prime[p]]


def distinct_prime_factors(value: int) -> list[int]:
    factors: list[int] = []
    d = 2
    while d * d <= value:
        if value % d == 0:
            factors.append(d)
            while value % d == 0:
                value //= d
        d += 1 if d == 2 else 2
    if value > 1:
        factors.append(value)
    return factors


def factorization(value: int) -> list[tuple[int, int]]:
    answer: list[tuple[int, int]] = []
    value = abs(value)
    d = 2
    while d * d <= value:
        if value % d == 0:
            exponent = 0
            while value % d == 0:
                value //= d
                exponent += 1
            answer.append((d, exponent))
        d += 1 if d == 2 else 2
    if value > 1:
        answer.append((value, 1))
    return answer


def primitive_root(p: int) -> int:
    factors = distinct_prime_factors(p - 1)
    for generator in range(2, p):
        if all(pow(generator, (p - 1) // ell, p) != 1 for ell in factors):
            return generator
    raise AssertionError(f"no primitive root modulo {p}")


def subgroup(p: int, n: int) -> list[int]:
    generator = primitive_root(p)
    zeta = pow(generator, (p - 1) // n, p)
    values = [pow(zeta, j, p) for j in range(n)]
    assert len(set(values)) == n and pow(zeta, n // 2, p) == p - 1
    return values


def signature_fibres(p: int, n: int, support: list[int]) -> dict[int, list[int]]:
    fibres: dict[int, list[int]] = defaultdict(list)
    for x in support:
        if x != 1:
            fibres[pow((x - 1) % p, n, p)].append(x)
    return dict(fibres)


def collision_formula(p: int, fibres: dict[int, list[int]]) -> int:
    total = 0
    for fibre in fibres.values():
        k = len(fibre)
        self_inverse = sum(1 for x in fibre if x * x % p == 1)
        assert self_inverse in (0, 1)
        total += k * k - 2 * k + self_inverse
    return total


def direct_accidents(p: int, support: list[int]) -> int:
    support_set = set(support)
    total = 0
    for a in support:
        for b in support:
            c = (a + b - 1) % p
            if c not in support_set:
                continue
            lawful = a == 1 or b == 1 or (c == p - 1 and b == (-a) % p)
            total += not lawful
    return total


def witness(p: int, support: list[int], fibres: dict[int, list[int]]) -> tuple[int, ...]:
    support_set = set(support)
    for signature, fibre in sorted(fibres.items()):
        for x in fibre:
            for y in fibre:
                if y == x or y == pow(x, p - 2, p):
                    continue
                h = (x - 1) * pow((y - 1) % p, p - 2, p) % p
                c = h * y % p
                assert x in support_set and h in support_set and c in support_set
                assert (x + h - c - 1) % p == 0
                assert x != 1 and h != 1 and not (c == p - 1 and h == (-x) % p)
                return signature, x, y, h, c
    raise AssertionError("positive collision count without witness")


def compact(values: list[int]) -> str:
    if len(values) <= 18:
        return str(values)
    return f"{values[:12]} ... {values[-5:]}"


def k8(value: int) -> int:
    return value**3 + 120 * value**2 - 2160 * value - 256


def main() -> int:
    primes = prime_sieve(LIMIT)
    all_bad: dict[int, list[tuple[int, int, tuple[int, ...]]]] = {}
    checked_bad = 0

    print("## ANT46 exact signature quotient: small-prime falsification census")
    print(f"scan: dyadic n={ORDERS}, primes p <= {LIMIT}, p == 1 (mod n)")
    for n in ORDERS:
        bad: list[tuple[int, int, tuple[int, ...]]] = []
        eligible = 0
        for p in primes:
            if p % n != 1:
                continue
            eligible += 1
            support = subgroup(p, n)
            fibres = signature_fibres(p, n, support)
            for x in support:
                if x != 1:
                    assert pow((x - 1) % p, n, p) == pow(
                        (pow(x, p - 2, p) - 1) % p, n, p
                    )
            count = collision_formula(p, fibres)
            if count:
                direct = direct_accidents(p, support)
                assert direct == count
                checked_bad += 1
                if pow(p - 3, n, p) != 1:
                    assert count % 12 == 0
                bad.append((p, count, witness(p, support, fibres)))
        all_bad[n] = bad
        bad_primes = [p for p, _count, _witness in bad]
        max_count = max((count for _p, count, _witness in bad), default=0)
        print(
            f"n={n:3d}: eligible={eligible:4d}, bad={len(bad):3d}, "
            f"max_count={max_count:5d}, primes={compact(bad_primes)}"
        )
        if bad:
            for label, row in (("first", bad[0]), ("last", bad[-1])):
                p, count, (signature, x, y, h, c) = row
                print(
                    f"  {label} witness p={p}, count={count}: kappa={signature}, "
                    f"(x,y,h;c)=({x},{y},{h};{c})"
                )

    print(f"cross-check: direct O(n^2) enumeration matched fibre formula at {checked_bad} bad cells")

    print("\n## Naive statements falsified")
    first_bad = {n: bad[0][0] for n, bad in all_bad.items() if bad}
    print(f"'all dyadic root subgroups are clean': false; first bad primes={first_bad}")
    above_cubic = [(p, count) for p, count, _ in all_bad[32] if p > 32**3]
    assert above_cubic
    print(f"'p > n^3 implies clean': false at n=32; witnesses={above_cubic}")
    four_packets = [
        (n, p, count)
        for n, bad in all_bad.items()
        for p, count, _ in bad
        if count % 12 != 0
    ]
    assert four_packets
    assert all(pow(p - 3, n, p) == 1 for n, p, _count in four_packets)
    print(
        "'every nonempty accident set has size divisible by 12' without the -3 exclusion: "
        f"false; exceptional cells begin {four_packets[:8]}"
    )
    print("all scanned cells with -3 outside H and an accident had count divisible by 12")

    print("\n## n=8 canonical quotient polynomial")
    # For n=8, the three nontrivial inversion classes have signatures which are roots of K8.
    for p in primes:
        if p % 8 != 1:
            continue
        support = subgroup(p, 8)
        representatives: list[int] = []
        seen: set[int] = set()
        for x in support:
            if x in (1, p - 1) or x in seen:
                continue
            xinv = pow(x, p - 2, p)
            seen.update((x, xinv))
            representatives.append(x)
        assert len(representatives) == 3
        assert all(k8(pow((x - 1) % p, 8, p)) % p == 0 for x in representatives)
    b, c, d = 120, -2160, -256
    discriminant = b * b * c * c - 4 * c**3 - 4 * b**3 * d - 27 * d * d + 18 * b * c * d
    self_value = k8(2**8)
    relevant = sorted(
        ell
        for ell, _exponent in factorization(discriminant * self_value)
        if ell % 8 == 1
    )
    assert relevant == [17, 41]
    assert [p for p, _count, _witness in all_bad[8]] == relevant
    print("K8(T)=T^3+120*T^2-2160*T-256 verified on every scanned order-8 subgroup")
    print(f"Disc(K8)={discriminant}, factorization={factorization(discriminant)}")
    print(f"K8(2^8)={self_value}, factorization={factorization(self_value)}")
    print("relevant factors ==1 mod 8 are exactly [17, 41], exactly the bad-prime census")

    print("\nVERDICT: exact quotient and fibre-count identities pass; universal cleanliness and")
    print("cubic-size shortcuts are refuted.  Production needs a prime-specific canonical")
    print("K_n discriminant/evaluation certificate or genuinely stronger arithmetic input.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
