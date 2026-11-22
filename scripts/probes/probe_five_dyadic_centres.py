#!/usr/bin/env python3
"""Check the sharp four-site example and the finite-field counting certificates."""

from math import comb

P1 = 365375409332725729550921208179070755120141565953
P2 = 730750818665451459101842416358141509841924915201
LENGTH = 2**30


def multiply(first, second):
    """Multiply in Z[Z]/(Z^16+1), which realizes the 32nd cyclotomic ring."""
    result = [0] * 16
    for i, a in enumerate(first):
        for j, b in enumerate(second):
            index = i + j
            result[index % 16] += (-1 if index >= 16 else 1) * a * b
    return result


def locator(support, site):
    result = [1] + [0] * 15
    for root in support:
        factor = [0] * 16
        factor[site % 16] += 1 if site < 16 else -1
        factor[root % 16] -= 1 if root < 16 else -1
        result = multiply(result, factor)
    return result


def verify_four_sites():
    a = {5, 11, 12, 14, 21, 23, 24, 30}
    b = {6, 7, 8, 13, 22, 27, 28, 29}
    assert len(a) == len(b) == 8 and not a & b
    assert not (a | b) & set(range(5))
    pa, pb = locator(a, 0), locator(b, 0)
    for i in range(1, 5):
        left = multiply(locator(a, i), pb)
        right = multiply(locator(b, i), pa)
        assert (left == right) == (i < 4)
    print("32nd roots: equal at 0,1,2,3 and unequal at 4")


def verify_bounds():
    choices = comb(4096, 1024)
    assert 2**3316 < choices
    for name, q, bits, t, r, s, one_parity in (
        ("first", P1 - 1, 158, 5473612, 21333, 214, 2692786),
        ("second", P2 - 1, 159, 5439375, 28089, 280, 2675850),
        ("joint", (P1 - 1) * (P2 - 1), 317, 2735180, 41601, 208, 1342146),
    ):
        blocks = (LENGTH - t) // 4096
        assert blocks * 1024 < LENGTH // 4
        assert q**1024 < 2 ** (1024 * bits + 1)
        assert (t - 1) * (1024 * bits + 1) < 3316 * blocks * 1024
        assert q**s < 3**r and (one_parity - 1) * r <= LENGTH // 4 * s
        print(f"{name}: {t:,} mixed centres, {blocks*1024:,} degree ceiling; "
              f"{one_parity:,} one-parity centres")
    assert (P2 - 1)**2 < 3**256
    assert (P2 - 1)**4 < comb(1019, 255)


if __name__ == "__main__":
    verify_four_sites()
    verify_bounds()
