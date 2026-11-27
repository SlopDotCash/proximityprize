#!/usr/bin/env python3
"""Exact verification of DyadicSplitPencilSqrtBound.lean caps and m^2 < 3 * 2^k across k = 6..60."""


def depth_entry(L: int) -> int:
    return 11 if L == 2 else 3 * (2**L) - 3


def bound(k: int, L: int, F: int) -> int:
    return max(depth_entry(L) - 1, (2 ** (k - L)) // F + 2 ** (L + 1) - 4)


def main():
    assert bound(6, 2, 3) == 10
    assert bound(6, 2, 4) == 10
    assert bound(7, 2, 3) == 14
    assert bound(7, 2, 4) == 12
    assert bound(8, 3, 3) == 22
    assert bound(8, 3, 4) == 20
    assert bound(29, 13, 3) == 38225
    assert bound(29, 13, 4) == 32764
    assert bound(30, 14, 3) == 54609
    assert bound(30, 13, 4) == 49148
    assert 2 * 38225 < 268435454
    assert 49148 < 134217727

    # Verify m^2 < 3 * 2^k at L = (k - 2) // 2 for ALL k = 6..60
    for k in range(6, 61):
        L = (k - 2) // 2
        assert 2 <= L and L + 2 <= k
        m3 = bound(k, L, 3)
        m4 = bound(k, L, 4)
        assert m3 * m3 < 3 * (2**k), f"Failed at k={k}: m3={m3}"
        assert m4 <= m3
    print("PASS: All concrete caps (mu_64..mu_{2^30}) and universal m^2 < 3 * 2^k (k = 6..60) verified exact!")


if __name__ == "__main__":
    main()
